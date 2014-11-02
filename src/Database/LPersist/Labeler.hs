{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, OverloadedStrings #-}

module Database.LPersist.Labeler (mkLabels) where

import Control.Applicative
import Control.Monad
import Data.Attoparsec.Text
import qualified Data.Char as Char
import qualified Data.List as List
import Data.Text (Text)
import qualified Data.Text as Text
import Database.Persist.Types
import Language.Haskell.TH
import Prelude

-- | Functions that use TH to generate labeling code. 
-- All examples in this documentation reference the following Persist model:
--
--   User
--       ident Text
--       password Text
--       email Text <Const Admin || Id, Id, _>
--       admin Bool
--   
--       UniqueEmail email
--       deriving Typeable

mkLabels :: String -> [EntityDef] -> Q [Dec]
mkLabels labelS ents = 
    let entsL = map toLEntityDef ents in
    let labelFs' = concat $ map (mkLabelEntity' labelType) entsL in
    do
    labelFs <- mapM (mkLabelEntity labelType) entsL
    lEntityInstance <- mapM (mkLEntityInstance labelType) entsL
    protected <- mapM (mkProtectedEntity labelType) entsL
    protectedInstance <- mapM (mkProtectedEntityInstance labelType) entsL
    let serializedLEntityDef = concat $ map mkSerializedLEntityDef entsL
    return $ concat [concat labelFs, labelFs', lEntityInstance, protected, protectedInstance, serializedLEntityDef]

    where
        labelType = 
            case Text.words $ Text.pack labelS of
                [] ->
                    error $ "Label `" ++ labelS ++ "` not found"
                conT:rest ->
                    if Text.length conT <= 1 || Char.isLower (Text.head conT) then
                        error $ "Invalid label type constructor `" ++ (Text.unpack conT) ++ "`"
                    else
                        let con = ConT $ mkName $ Text.unpack conT in
                        List.foldl' (\acc typ -> AppT acc (ConT (mkName (Text.unpack typ)))) con rest



-- | Create protected ADTs for the models in Persist's DSL. 
-- Ex: ProtectedUser is created for protected version of User.
--
-- data ProtectedUser = ProtectedUser {
--         pUserIdent :: Text
--       , pUserPassword :: Text
--       , pUserEmail :: Labeled (DCLabel Principal) Text
--       , pUserAdmin :: Bool
--     }

mkProtectedEntity :: Type -> LEntityDef -> Q Dec
mkProtectedEntity labelType ent =
    let pFields = map mkProtectedField (lEntityFields ent) in
    return $ DataD [] pName [] [RecC pName pFields] []

    where
        eName = lEntityHaskell ent
        pName = mkName $ "Protected" ++ eName
        mkProtectedField field = 
            let fName = mkName $ 'p':(eName ++ (headToUpper (lFieldHaskell field))) in
            let strict = if lFieldStrict field then IsStrict else NotStrict in
            let rawType = fieldTypeToType $ lFieldType field in
            let typ = case lFieldLabelAnnotations field of
                  Nothing ->
                    rawType
                  Just _ ->
                    AppT (AppT (ConT (mkName "Labeled")) labelType) rawType
            in
            (fName, strict, typ)



-- | Create LEntity instance for a given entity. Joins all field label calls
-- Ex:
--
-- instance LEntity (DCLabel Principal) User where
--     getLabelRead _e = 
--         readLabelUserEmail _e
--     getLabelWrite _e =
--         writeLabelUserEmail _e
--     getLabelCreate _e =
--         createLabelUserEmail _e

mkLEntityInstance :: Type -> LEntityDef -> Q Dec
mkLEntityInstance labelType ent = 
    let expr = List.foldl' mkStmts Nothing (lEntityFields ent) in
    let (rExpr, wExpr, cExpr) = case expr of 
          Nothing ->
            ( bottom, bottom, bottom)
          Just exprs ->
            exprs
    in
    let funcs = [
            FunD (mkName "getLabelRead") [Clause [VarP e] (NormalB rExpr) []],
            FunD (mkName "getLabelWrite") [Clause [VarP e] (NormalB wExpr) []],
            FunD (mkName "getLabelCreate") [Clause [VarP e] (NormalB cExpr) []]
          ]
    in
    return $ InstanceD [] (AppT (AppT (ConT (mkName "LEntity")) labelType) (ConT (mkName eName))) funcs

    where
        eName = lEntityHaskell ent
        e = mkName "_e"
        bottom = VarE $ mkName "bottom"
        appJoin = AppE . (AppE (VarE (mkName "lub")))
        mkStmts acc field = case lFieldLabelAnnotations field of
            Nothing -> 
                acc
            _ -> 
                let baseName = eName ++ (headToUpper (lFieldHaskell field)) in
                let rExpr = AppE (VarE (mkName ("readLabel"++baseName))) (VarE e) in
                let wExpr = AppE (VarE (mkName ("writeLabel"++baseName))) (VarE e) in
                let cExpr = AppE (VarE (mkName ("createLabel"++baseName))) (VarE e) in
                Just $ case acc of
                    Nothing ->
                        ( rExpr, wExpr, cExpr)
                    Just (rAcc, wAcc, cAcc) ->
                        ( appJoin rExpr rAcc, appJoin wExpr wAcc, appJoin cExpr cAcc)



-- | Creates functions that get labels for each field in an entity. 
-- Ex:
--
-- readLabelUserEmail :: Entity User -> DCLabel Principal
-- readLabelUserEmail (Entity _eId _entity) =
--     ((toConfidentialityLabel "Admin") `glb` (toConfidentialityLabel _eId))
--
-- createLabelUserEmail :: Entity User -> DCLabel Principal
-- createLabelUserEmail (Entity _eId _entity) = 
--     toIntegrityLabel _eId
--
-- writeLabelUserEmail :: Entity User -> DCLabel Principal
-- writeLabelUserEmail (Entity _eId _entity) = 
--     bottom

mkLabelEntity :: Type -> LEntityDef -> Q [Dec]
mkLabelEntity labelType ent = 
    let labelFs = map mkLabelField (lEntityFields ent) in
    return $ concat labelFs
    
    where
        eName = lEntityHaskell ent
        toConfLabel = VarE $ mkName "toConfidentialityLabel"
        toIntegLabel = VarE $ mkName "toIntegrityLabel"
        bottom = VarE $ mkName "bottom"
        appMeet = AppE . (AppE (VarE (mkName "glb")))
        combAnnotations f eId e l = case l of
            [] ->
                bottom
            h:t -> 
                let appF ann = case ann of
                      LAId ->
                        AppE f $ VarE eId
                      LAConst c ->
                        AppE f $ SigE (LitE $ StringL c) $ ConT $ mkName "String"
                      LAField fName ->
                        let getter = VarE $ mkName $ (headToLower eName) ++ (headToUpper fName) in
                        AppE f $ AppE getter $ VarE e
                in
                List.foldl' (\acc ann -> appMeet acc $ appF ann) (appF h) t
            
        mkLabelField field = 
            case lFieldLabelAnnotations field of
                Nothing ->
                    []
                Just ( readAnns, writeAnns, createAnns) ->
                    let eId = mkName "_eId" in
                    let e = mkName "_entity" in
                    let baseName = eName ++ (headToUpper (lFieldHaskell field)) in
                    let readName = mkName $ "readLabel" ++ baseName in
                    let writeName = mkName $ "writeLabel" ++ baseName in
                    let createName = mkName $ "createLabel" ++ baseName in
                    let readSig = SigD readName $ AppT (AppT ArrowT (AppT (ConT (mkName "Entity")) (ConT (mkName eName)))) labelType in
                    let rBody = combAnnotations toConfLabel eId e readAnns in
                    let readDef = FunD readName [Clause [ConP (mkName "Entity") [VarP eId, VarP e]] (NormalB rBody) []] in
                    let writeSig = SigD writeName $ AppT (AppT ArrowT (AppT (ConT (mkName "Entity")) (ConT (mkName eName)))) labelType in
                    let wBody = combAnnotations toIntegLabel eId e writeAnns in
                    let writeDef = FunD writeName [Clause [ConP (mkName "Entity") [VarP eId, VarP e]] (NormalB wBody) []] in
                    let createSig = SigD createName $ AppT (AppT ArrowT ( ConT (mkName eName))) labelType in
                    let cBody = combAnnotations toIntegLabel eId e createAnns in
                    let createDef = FunD createName [Clause [VarP e] (NormalB cBody) []] in
                    [readSig,readDef,writeSig,writeDef,createSig,createDef]



-- | Similar to mkLabelEntity, except this function creates code that returns the labels given what the label depends on instead of the entire entity. 
-- Ex:
--
-- readLabelUserEmail' :: UserId -> DCLabel Principal
-- readLabelUserEmail' uId = 
--     ((toConfidentialityLabel "Admin") `glb` (toConfidentialityLabel uId))
--
-- writeLabelUserEmail' :: UserId -> DCLabel Principal
-- writeLabelUserEmail' uId = 
--     (toIntegrityLabel uId)
--
-- createLabelUserEmail' :: DCLabel Principal
-- createLabelUserEmail' = 
--     bottom

mkLabelEntity' :: Type -> LEntityDef -> [Dec]
mkLabelEntity' labelType ent =
    let labelFs = map mkLabelField' (lEntityFields ent) in
    concat labelFs

    where
        eName = lEntityHaskell ent
        toConfLabel = VarE $ mkName "toConfidentialityLabel"
        toIntegLabel = VarE $ mkName "toIntegrityLabel"
        bottom = VarE $ mkName "bottom"
        appMeet = AppE . (AppE (VarE (mkName "glb")))
        mkType =
            let helper annotation acc = case annotation of
                  LAConst _ ->
                    acc
                  LAId ->
                    let name = mkName $ eName ++ "Id" in
                    AppT (AppT ArrowT (ConT name)) acc
                  LAField s -> 
                    let typ = getLEntityFieldType ent s in
                    AppT (AppT ArrowT typ) acc
            in
            List.foldr helper labelType
        mkPattern = 
            let helper annotation acc = case annotation of
                  LAConst _ ->
                    acc
                  LAId -> 
                    (VarP $ mkName "_id"):acc
                  LAField s ->
                    (VarP $ mkName $ "_" ++ s):acc
            in
            List.foldr helper []
        mkBody f anns = case anns of
            [] -> 
                bottom
            h:t -> 
                let appF ann = case ann of
                      LAId ->
                        AppE f $ VarE $ mkName "_id"
                      LAConst c ->
                        AppE f $ SigE (LitE $ StringL c) $ ConT $ mkName "String"
                      LAField fName ->
                        AppE f $ VarE $ mkName $ "_" ++ fName
                in
                List.foldl' (\acc ann -> appMeet acc $ appF ann) (appF h) t
        mkLabelField' field = 
            case lFieldLabelAnnotations field of
                Nothing ->
                    []
                Just ( readAnns, writeAnns, createAnns) ->
                    let baseName = eName ++ (headToUpper (lFieldHaskell field)) in
                    let readName = mkName $ "readLabel" ++ baseName ++ "'" in
                    let writeName = mkName $ "writeLabel" ++ baseName ++ "'" in
                    let createName = mkName $ "createLabel" ++ baseName ++ "'" in
                    let readSig = SigD readName $ mkType readAnns in
                    let readDef = FunD readName [Clause (mkPattern readAnns) (NormalB $ mkBody toConfLabel readAnns) []] in
                    let writeSig = SigD writeName $ mkType writeAnns in
                    let writeDef = FunD writeName [Clause (mkPattern writeAnns) (NormalB $ mkBody toIntegLabel writeAnns) []] in
                    let createSig = SigD createName $ mkType createAnns in
                    let createDef = FunD createName [Clause (mkPattern createAnns) (NormalB $ mkBody toIntegLabel createAnns) []] in
                    [readSig, readDef, writeSig, writeDef, createSig, createDef]



-- | Create ProtectedEntity instance for given entity.
-- Ex:
--
-- instance ProtectedEntity (DCLabel Principal) User ProtectedUser where
--     toProtected _entity@(Entity _eId _e) = do
--         let ident = userIdent _e
--         let password = userPassword _e
--         email <- 
--             let l = readLabelUserEmail _entity in
--             toLabeledTCB l $ do
--                 taintLabel l
--                 return $ userEmail _e
--          let admin = userAdmin _e
--          return $ ProtectedUser ident password email admin

mkProtectedEntityInstance :: Type -> LEntityDef -> Q Dec
mkProtectedEntityInstance labelType ent = do
    ( fStmts, fExps) <- foldM mkProtectedFieldInstance ([],[]) $ lEntityFields ent
    let recordCons = RecConE (mkName pName) fExps
    let body = DoE $ fStmts ++ [NoBindS (AppE (VarE (mkName "return")) recordCons)]
    let toProtected = FunD (mkName "toProtected") [Clause [AsP entity (ConP (mkName "Entity") [VarP eId,VarP e])] (NormalB body) []]
    return $ InstanceD [] (AppT (AppT (AppT (ConT (mkName "ProtectedEntity")) labelType) (ConT (mkName eName))) (ConT (mkName pName))) [toProtected]

    where 
        eName = lEntityHaskell ent
        pName = "Protected" ++ eName
        e = mkName "_e"
        eId = mkName "_eId"
        entity = mkName "_entity"

        mkProtectedFieldInstance :: ([Stmt],[FieldExp]) -> LFieldDef -> Q ([Stmt],[FieldExp])
        mkProtectedFieldInstance (sAcc, fAcc) field = do
            let fName = lFieldHaskell field
            let getter = mkName $ (headToLower eName) ++ (headToUpper fName)
            vName <- newName "v"
            let setter = mkName $ 'p':(eName ++ (headToUpper fName))
            let newF = (setter, VarE vName)
            newS <- case lFieldLabelAnnotations field of
                  Nothing ->
                    return $ LetS [ValD (VarP vName) (NormalB (AppE (VarE getter) (VarE e))) []]
                  Just _ -> do
                    lName <- newName "l"
                    let taintRead = mkName $ "readLabel" ++ eName ++ (headToUpper fName)
                    let lDec = ValD (VarP lName) (NormalB (AppE (VarE taintRead) (VarE entity))) []
                    return $ BindS (VarP vName) $ LetE [lDec] $ AppE (AppE (VarE (mkName "toLabeledTCB")) (VarE lName)) $ DoE [
                            NoBindS $ AppE (VarE (mkName "taintLabel")) (VarE lName),
                            NoBindS $ AppE (VarE (mkName "return")) (AppE (VarE getter) (VarE e))
                          ]
            return ( (newS:sAcc), (newF:fAcc))



-- | Serialize LEntityDefs so that lsql can access them in other modules. 
-- Ex:
--
-- lEntityDefUser = LEntityDef "User" [LFieldDef "ident" (FTTypeCon "Text") True Nothing, ...]
mkSerializedLEntityDef :: LEntityDef -> [Dec]
mkSerializedLEntityDef ent = 
    let str = LitE $ StringL $ lEntityHaskell ent in
    let fields = mkSerializedLEntityDef $ lEntityFields ent in
    let body = AppE (AppE (ConE 'LEntityDef) str) fields in
    let name = mkName $ "lEntityDef" ++ (lEntityHaskell ent) in
    let sig = SigD name $ ConT ''LEntityDef in
    let def = ValD (VarP name) (NormalB body) [] in
    [ sig, def]

    where
        mkSerializedText t = SigE (LitE $ StringL $ Text.unpack t) (ConT ''Text)
        mkSerializedFieldType typ = case typ of
            FTTypeCon moduleM' name' ->
                let moduleM = maybe (ConE 'Nothing) (\m -> AppE (ConE 'Just) (mkSerializedText m)) moduleM' in
                let name = mkSerializedText name' in
                AppE (AppE (ConE 'FTTypeCon) moduleM) name
            FTApp typ1' typ2' ->
                let typ1 = mkSerializedFieldType typ1' in
                let typ2 = mkSerializedFieldType typ2' in
                AppE (AppE (ConE 'FTApp) typ1) typ2
            FTList typ' ->
                let typ = mkSerializedFieldType typ' in
                AppE (ConE 'FTList) typ
        mkSerializedLabelAnnotation la = case la of 
            LAId ->
                ConE 'LAId
            LAConst s ->
                AppE (ConE 'LAConst) (LitE $ StringL s)
            LAField s -> 
                AppE (ConE 'LAField) (LitE $ StringL s)
        mkSerializedLEntityDef fields' = 
            let helper field = 
                  let name = LitE $ StringL $ lFieldHaskell field in
                  let typ = mkSerializedFieldType $ lFieldType field in
                  let strict = ConE $ if lFieldStrict field then 'True else 'False in
                  let anns = maybe (ConE 'Nothing) (\( r', w', c') -> 
                            let r = ListE $ map mkSerializedLabelAnnotation r' in
                            let w = ListE $ map mkSerializedLabelAnnotation w' in
                            let c = ListE $ map mkSerializedLabelAnnotation c' in
                            AppE (ConE 'Just) $ TupE [ r, w, c]
                        ) $ lFieldLabelAnnotations field 
                  in
                  AppE (AppE (AppE (AppE (ConE 'LFieldDef) name) typ) strict) anns
            in
            ListE $ map helper fields'

data LEntityDef = LEntityDef
    { lEntityHaskell :: !String
--     , lEntityDB      :: !String
--     , lEntityId      :: !FieldDef
--     , lEntityAttrs   :: ![Attr]
    , lEntityFields  :: ![LFieldDef]
--     , lEntityUniques :: ![UniqueDef]
--     , lEntityForeigns:: ![ForeignDef]
--     , lEntityDerives :: ![Text]
--     , lEntityExtra   :: !(Map Text [ExtraLine])
--     , lEntitySum     :: !Bool
    }

data LFieldDef = LFieldDef
    { lFieldHaskell   :: !String -- ^ name of the field
--    , lFieldDB        :: !String
    , lFieldType      :: !FieldType
--    , lFieldSqlType   :: !SqlType
--    , lFieldAttrs     :: ![Attr]    -- ^ user annotations for a field
    , lFieldStrict    :: !Bool      -- ^ a strict field in the data type. Default: true
--    , lFieldReference :: !ReferenceDef
    , lFieldLabelAnnotations :: !(Maybe ([LabelAnnotation],[LabelAnnotation],[LabelAnnotation]))
    }
    deriving (Show, Eq, Read, Ord)

toLEntityDef :: EntityDef -> LEntityDef
toLEntityDef ent = LEntityDef {
        lEntityHaskell = Text.unpack $ unHaskellName $ entityHaskell ent
--      , lEntityDB = Text.unpack $ unDBName $ entityDB ent
      , lEntityFields = map toLFieldDef (entityFields ent)
    }

toLFieldDef :: FieldDef -> LFieldDef
toLFieldDef f = LFieldDef {
        lFieldHaskell = Text.unpack $ unHaskellName $ fieldHaskell f
--       , lFieldDB = Text.unpack $ unDBName $ fieldDB f
      , lFieldType = fieldType f
      , lFieldStrict = fieldStrict f
      , lFieldLabelAnnotations = labels
    }

    where
        labels = 
            let attrs = fieldAttrs f in
            List.foldl' (\acc attr -> 
                let ( prefix, affix) = Text.splitAt 9 attr in
                if acc /= Nothing || prefix /= "chevrons=" then
                    acc
                else
                    Just $ parseChevrons affix
              ) Nothing attrs

fieldTypeToType :: FieldType -> Type
fieldTypeToType ft = case ft of
    FTTypeCon Nothing con -> 
        ConT $ mkName $ Text.unpack con
    _ ->
        error "TODO: will this ever happen??"

getLEntityFieldType :: LEntityDef -> String -> Type
getLEntityFieldType ent fName = 
    let ftype = List.foldl' (\acc f -> case (acc, lFieldHaskell f) of 
            (Nothing, s) | s == fName -> 
                Just $ fieldTypeToType $ lFieldType f
            _ ->
                acc
          ) Nothing $ lEntityFields ent 
    in
    case ftype of 
        Nothing ->
            error $ "getLEntityFieldType: Could not find find field `" ++ fName ++"` in entity `"++ (lEntityHaskell ent) ++"`"
        Just f ->
            f

-- Parse chevrons
-- C = < L , L , L >
-- L = K | _
-- K = A || K | A
-- A = Id | Const name | Field name

parseChevrons :: Text -> ([LabelAnnotation],[LabelAnnotation],[LabelAnnotation])
parseChevrons s = case parseOnly parseC s of
    Left err ->
        error $ "Could not parse labels in chevrons: " ++ err
    Right res ->
        res

    where
        parseC = do
            read <- parseL
            skipSpace
            _ <- char ','
            write <- parseL
            skipSpace
            _ <- char ','
            create <- parseL
            return (read,write,create)

        parseL = (skipSpace >> char '_' >> return []) <|> parseK
        
        parseK = do
            la <- parseA
            tail <- (do
                skipSpace
                _ <- char '|'
                _ <- char '|'
                parseK
              ) <|> (return [])

            return $ la:tail

        parseA = do
            skipSpace
            constr <- takeAlphaNum
            case constr of
                "Id" -> 
                    return LAId
                "Const" -> do
                    skipSpace
                    name <- takeAlphaNum
                    return $ LAConst $ Text.unpack name
                "Field" -> do
                    skipSpace
                    name <- takeAlphaNum
                    return $ LAField $ Text.unpack name
                _ -> 
                    fail $ "Unknown keyword `" ++ (Text.unpack constr) ++ "` in parseChevrons. Use `Id`, `Const`, `Field`, or `_`"
        
        takeAlphaNum = takeWhile1 Char.isAlphaNum
            
headToUpper :: String -> String
headToUpper (h:t) = (Char.toUpper h):t
headToUpper s = error $ "Invalid name `" ++ s ++ "`"

headToLower :: String -> String
headToLower (h:t) = (Char.toLower h):t
headToLower s = error $ "Invalid name `" ++ s ++ "`"

data LabelAnnotation = 
    LAId
  | LAConst String
  | LAField String
    deriving (Show, Eq, Read, Ord)

