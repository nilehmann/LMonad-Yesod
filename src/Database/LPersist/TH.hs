{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
-- {-# LANGUAGE RankNTypes #-}
-- {-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-missing-fields #-}
-- overlapping instances is for automatic lifting
-- while avoiding an orphan of Lift for Text
{-# LANGUAGE OverlappingInstances #-}
-- | This module provides utilities for creating backends. Regular users do not
-- need to use this module.
module Database.LPersist.TH
    ( -- * Parse entity defs
      lPersistWith
    , lPersistUpperCase
    , lPersistLowerCase
    , lPersistFileWith
    ) where

import Prelude hiding ((++), take, concat, splitAt, exp)
import Database.Persist
import Database.Persist.Quasi
import Database.LPersist.Quasi
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Instances.TH.Lift ()
import qualified System.IO as SIO
import Data.Text (pack, Text, unpack, concat, stripPrefix, stripSuffix)
import qualified Data.Text.IO as TIO
import Data.Maybe (listToMaybe, mapMaybe)
import qualified Data.Map as M
import Database.Persist.Sql (sqlType)
import Data.Proxy (Proxy (Proxy))
import Data.Int (Int64)

lPersistWith :: PersistSettings -> QuasiQuoter
lPersistWith ps = QuasiQuoter
    { quoteExp = parseReferences ps . pack
    }

-- | Apply 'persistWith' to 'upperCaseSettings'.
lPersistUpperCase :: QuasiQuoter
lPersistUpperCase = lPersistWith upperCaseSettings

-- | Apply 'persistWith' to 'lowerCaseSettings'.
lPersistLowerCase :: QuasiQuoter
lPersistLowerCase = lPersistWith lowerCaseSettings

-- | Same as 'persistWith', but uses an external file instead of a
-- quasiquotation.
lPersistFileWith :: PersistSettings -> FilePath -> Q Exp
lPersistFileWith ps fp = do
#ifdef GHC_7_4
    qAddDependentFile fp
#endif
    h <- qRunIO $ SIO.openFile fp SIO.ReadMode
    qRunIO $ SIO.hSetEncoding h SIO.utf8_bom
    s <- qRunIO $ TIO.hGetContents h
    parseReferences ps s

embedEntityDefsMap :: [EntityDef] -> (M.Map HaskellName EmbedEntityDef, [EntityDef])
embedEntityDefsMap rawEnts = (embedEntityMap, noCycleEnts)
  where
    noCycleEnts = map breakCycleEnt entsWithEmbeds
    -- every EntityDef could reference each-other (as an EmbedRef)
    -- let Haskell tie the knot
    embedEntityMap = constructEmbedEntityMap entsWithEmbeds
    entsWithEmbeds = map setEmbedEntity rawEnts
    setEmbedEntity ent = ent
        { entityFields = map (setEmbedField (entityHaskell ent) embedEntityMap) $ entityFields ent
        }

    -- self references are already broken
    -- look at every emFieldEmbed to see if it refers to an already seen HaskellName
    -- so start with entityHaskell ent and accumulate embeddedHaskell em
    breakCycleEnt entDef =
        let entName = entityHaskell entDef
         in entDef { entityFields = map (breakCycleField entName) $ entityFields entDef }

    breakCycleField entName f = case f of
        FieldDef { fieldReference = EmbedRef em } ->
            f { fieldReference = EmbedRef $ breakCycleEmbed [entName] em }
        _ ->
            f

    breakCycleEmbed ancestors em =
        em { embeddedFields = breakCycleEmField (emName : ancestors) <$> embeddedFields em
           }
        where
            emName = embeddedHaskell em

    breakCycleEmField ancestors emf = case embeddedHaskell <$> membed of
        Nothing -> emf
        Just embName -> if embName `elem` ancestors
            then emf { emFieldEmbed = Nothing, emFieldCycle = Just embName }
            else emf { emFieldEmbed = breakCycleEmbed ancestors <$> membed }
        where
            membed = emFieldEmbed emf

-- calls parse to Quasi.parse individual entities in isolation
-- afterwards, sets references to other entities
parseReferences :: PersistSettings -> Text -> Q Exp
parseReferences ps s = lift $
    map (mkEntityDefSqlTypeExp embedEntityMap entityMap) noCycleEnts
  where
    (embedEntityMap, noCycleEnts) = embedEntityDefsMap $ lParse ps s
    entityMap = constructEntityMap noCycleEnts

stripId :: FieldType -> Maybe Text
stripId (FTTypeCon Nothing t) = stripSuffix "Id" t
stripId _ = Nothing

-- foreignReference :: FieldDef -> Maybe HaskellName
-- foreignReference field = case fieldReference field of
--     ForeignRef ref _ -> Just ref
--     _              -> Nothing


-- fieldSqlType at parse time can be an Exp
-- This helps delay setting fieldSqlType until lift time
data EntityDefSqlTypeExp = EntityDefSqlTypeExp EntityDef SqlTypeExp [SqlTypeExp]
                           deriving Show

data SqlTypeExp = SqlTypeExp FieldType
                | SqlType' SqlType
                deriving Show

instance Lift SqlTypeExp where
    lift (SqlType' t)       = lift t
    lift (SqlTypeExp ftype) = return st
      where
        typ = ftToType ftype
        mtyp = ConT ''Proxy `AppT` typ
        typedNothing = SigE (ConE 'Proxy) mtyp
        st = VarE 'sqlType `AppE` typedNothing

data FieldsSqlTypeExp = FieldsSqlTypeExp [FieldDef] [SqlTypeExp]

instance Lift FieldsSqlTypeExp where
    lift (FieldsSqlTypeExp fields sqlTypeExps) =
        lift $ zipWith FieldSqlTypeExp fields sqlTypeExps

data FieldSqlTypeExp = FieldSqlTypeExp FieldDef SqlTypeExp
instance Lift FieldSqlTypeExp where
    lift (FieldSqlTypeExp (FieldDef{..}) sqlTypeExp) =
      [|FieldDef fieldHaskell fieldDB fieldType $(lift sqlTypeExp) fieldAttrs fieldStrict fieldReference fieldComments|]

instance Lift EntityDefSqlTypeExp where
    lift (EntityDefSqlTypeExp ent sqlTypeExp sqlTypeExps) =
        [|ent { entityFields = $(lift $ FieldsSqlTypeExp (entityFields ent) sqlTypeExps)
              , entityId = $(lift $ FieldSqlTypeExp (entityId ent) sqlTypeExp)
              }
        |]

instance Lift ReferenceDef where
    lift NoReference = [|NoReference|]
    lift (ForeignRef name ft) = [|ForeignRef name ft|]
    lift (EmbedRef em) = [|EmbedRef em|]
    lift (CompositeRef cdef) = [|CompositeRef cdef|]
    lift (SelfReference) = [|SelfReference|]

instance Lift EmbedEntityDef where
    lift (EmbedEntityDef name fields) = [|EmbedEntityDef name fields|]

instance Lift EmbedFieldDef where
    lift (EmbedFieldDef name em cyc) = [|EmbedFieldDef name em cyc|]

type EmbedEntityMap = M.Map HaskellName EmbedEntityDef

constructEmbedEntityMap :: [EntityDef] -> EmbedEntityMap
constructEmbedEntityMap =
    M.fromList . fmap (\ent -> (entityHaskell ent, toEmbedEntityDef ent))

type EntityMap = M.Map HaskellName EntityDef

constructEntityMap :: [EntityDef] -> EntityMap
constructEntityMap =
    M.fromList . fmap (\ent -> (entityHaskell ent, ent))

data FTTypeConDescr = FTKeyCon
    deriving Show

mEmbedded
    :: EmbedEntityMap
    -> FieldType
    -> Either (Maybe FTTypeConDescr) EmbedEntityDef
mEmbedded _ (FTTypeCon Just{} _) =
    Left Nothing
mEmbedded ents (FTTypeCon Nothing (HaskellName -> name)) =
    maybe (Left Nothing) Right $ M.lookup name ents
mEmbedded ents (FTList x) =
    mEmbedded ents x
mEmbedded ents (FTApp x y) =
    -- Key converts an Record to a RecordId
    -- special casing this is obviously a hack
    -- This problem may not be solvable with the current QuasiQuoted approach though
    if x == FTTypeCon Nothing "Key"
        then Left $ Just FTKeyCon
        else mEmbedded ents y

setEmbedField :: HaskellName -> EmbedEntityMap -> FieldDef -> FieldDef
setEmbedField entName allEntities field = field
    { fieldReference =
        case fieldReference field of
            NoReference ->
                case mEmbedded allEntities (fieldType field) of
                    Left _ ->
                        case stripId $ fieldType field of
                            Nothing ->
                                NoReference
                            Just name ->
                                case M.lookup (HaskellName name) allEntities of
                                    Nothing ->
                                        NoReference
                                    Just _ ->
                                        ForeignRef
                                            (HaskellName name)
                                            -- This can get corrected in mkEntityDefSqlTypeExp
                                            (FTTypeCon (Just "Data.Int") "Int64")
                    Right em ->
                        if embeddedHaskell em /= entName
                             then EmbedRef em
                        else if maybeNullable field
                             then SelfReference
                        else case fieldType field of
                                 FTList _ -> SelfReference
                                 _ -> error $ unpack $ unHaskellName entName <> ": a self reference must be a Maybe"
            existing ->
                existing
  }

mkEntityDefSqlTypeExp :: EmbedEntityMap -> EntityMap -> EntityDef -> EntityDefSqlTypeExp
mkEntityDefSqlTypeExp emEntities entityMap ent =
    EntityDefSqlTypeExp ent (getSqlType $ entityId ent) (map getSqlType $ entityFields ent)
  where
    getSqlType field =
        maybe
            (defaultSqlTypeExp field)
            (SqlType' . SqlOther)
            (listToMaybe $ mapMaybe (stripPrefix "sqltype=") $ fieldAttrs field)

    -- In the case of embedding, there won't be any datatype created yet.
    -- We just use SqlString, as the data will be serialized to JSON.
    defaultSqlTypeExp field =
        case mEmbedded emEntities ftype of
            Right _ ->
                SqlType' SqlString
            Left (Just FTKeyCon) ->
                SqlType' SqlString
            Left Nothing ->
                case fieldReference field of
                    ForeignRef refName ft ->
                        case M.lookup refName entityMap of
                            Nothing  -> SqlTypeExp ft
                            -- A ForeignRef is blindly set to an Int64 in setEmbedField
                            -- correct that now
                            Just ent' ->
                                case entityPrimary ent' of
                                    Nothing -> SqlTypeExp ft
                                    Just pdef ->
                                        case compositeFields pdef of
                                            [] -> error "mkEntityDefSqlTypeExp: no composite fields"
                                            [x] -> SqlTypeExp $ fieldType x
                                            _ -> SqlType' $ SqlOther "Composite Reference"
                    CompositeRef _ ->
                        SqlType' $ SqlOther "Composite Reference"
                    _ ->
                        case ftype of
                            -- In the case of lists, we always serialize to a string
                            -- value (via JSON).
                            --
                            -- Normally, this would be determined automatically by
                            -- SqlTypeExp. However, there's one corner case: if there's
                            -- a list of entity IDs, the datatype for the ID has not
                            -- yet been created, so the compiler will fail. This extra
                            -- clause works around this limitation.
                            FTList _ -> SqlType' SqlString
                            _ -> SqlTypeExp ftype
        where
            ftype = fieldType field

instance Lift EntityDef where
    lift EntityDef{..} =
        [|EntityDef
            entityHaskell
            entityDB
            entityId
            entityAttrs
            entityFields
            entityUniques
            entityForeigns
            entityDerives
            entityExtra
            entitySum
            entityComments
            |]
instance Lift FieldDef where
    lift (FieldDef a b c d e f g h) = [|FieldDef a b c d e f g h|]
instance Lift UniqueDef where
    lift (UniqueDef a b c d) = [|UniqueDef a b c d|]
instance Lift CompositeDef where
    lift (CompositeDef a b) = [|CompositeDef a b|]
instance Lift ForeignDef where
    lift (ForeignDef a b c d e f g) = [|ForeignDef a b c d e f g|]

instance Lift HaskellName where
    lift (HaskellName t) = [|HaskellName t|]
instance Lift DBName where
    lift (DBName t) = [|DBName t|]
instance Lift FieldType where
    lift (FTTypeCon Nothing t)  = [|FTTypeCon Nothing t|]
    lift (FTTypeCon (Just x) t) = [|FTTypeCon (Just x) t|]
    lift (FTApp x y) = [|FTApp x y|]
    lift (FTList x) = [|FTList x|]

instance Lift SqlType where
    lift SqlString = [|SqlString|]
    lift SqlInt32 = [|SqlInt32|]
    lift SqlInt64 = [|SqlInt64|]
    lift SqlReal = [|SqlReal|]
    lift (SqlNumeric x y) =
        [|SqlNumeric (fromInteger x') (fromInteger y')|]
      where
        x' = fromIntegral x :: Integer
        y' = fromIntegral y :: Integer
    lift SqlBool = [|SqlBool|]
    lift SqlDay = [|SqlDay|]
    lift SqlTime = [|SqlTime|]
    lift SqlDayTime = [|SqlDayTime|]
    lift SqlBlob = [|SqlBlob|]
    lift (SqlOther a) = [|SqlOther a|]

maybeNullable :: FieldDef -> Bool
maybeNullable fd = nullable (fieldAttrs fd) == Nullable ByMaybeAttr

ftToType :: FieldType -> Type
ftToType (FTTypeCon Nothing t) = ConT $ mkName $ unpack t
-- This type is generated from the Quasi-Quoter.
-- Adding this special case avoids users needing to import Data.Int
ftToType (FTTypeCon (Just "Data.Int") "Int64") = ConT ''Int64
ftToType (FTTypeCon (Just m) t) = ConT $ mkName $ unpack $ concat [m, ".", t]
ftToType (FTApp x y) = ftToType x `AppT` ftToType y
ftToType (FTList x) = ListT `AppT` ftToType x
