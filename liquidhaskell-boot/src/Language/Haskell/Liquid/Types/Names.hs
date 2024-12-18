{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.Liquid.Types.Names
  ( lenLocSymbol
  , anyTypeSymbol
  , selfSymbol
  , LogicName (..)
  , LHResolvedName (..)
  , LHName (..)
  , LHNameSpace (..)
  , LHThisModuleNameFlag (..)
  , makeResolvedLHName
  , getLHGHCName
  , getLHNameResolved
  , getLHNameSymbol
  , lhNameToResolvedSymbol
  , lhNameToUnqualifiedSymbol
  , makeGHCLHName
  , makeGHCLHNameFromId
  , makeGHCLHNameLocated
  , makeGHCLHNameLocatedFromId
  , makeLocalLHName
  , makeLogicLHName
  , makeGeneratedLogicLHName
  , makeUnresolvedLHName
  , mapLHNames
  , mapMLocLHNames
  , maybeReflectedLHName
  , reflectGHCName
  , reflectLHName
  , updateLHNameSymbol
  ) where

import Control.DeepSeq
import qualified Data.Binary as B
import Data.Data (Data, gmapM, gmapT)
import Data.Generics (extM, extT)
import Data.Hashable
import Data.String (fromString)
import qualified Data.Text                               as Text
import GHC.Generics
import GHC.Show
import GHC.Stack
import Language.Fixpoint.Types
import Language.Haskell.Liquid.GHC.Misc (locNamedThing) -- Symbolic GHC.Name
import qualified Liquid.GHC.API as GHC

-- RJ: Please add docs
lenLocSymbol :: Located Symbol
lenLocSymbol = dummyLoc $ symbol ("autolen" :: String)

anyTypeSymbol :: Symbol
anyTypeSymbol = symbol ("GHC.Prim.Any" :: String)

selfSymbol :: Symbol
selfSymbol = symbol ("liquid_internal_this" :: String)

-- | A name for an entity that does not exist in Haskell
--
-- For instance, this can be used to represent predicate aliases
-- or uninterpreted functions.
data LogicName =
    LogicName
       -- | Unqualified symbol
      !Symbol
        -- | Module where the entity was defined
      !GHC.Module
        -- | If the named entity is the reflection of some Haskell name
      !(Maybe GHC.Name)
    | GeneratedLogicName Symbol
  deriving (Data, Eq, Generic)

-- | A name whose procedence is known.
data LHResolvedName
    = LHRLogic !LogicName
    | LHRGHC !GHC.Name    -- ^ A name for an entity that exists in Haskell
    | LHRLocal !Symbol    -- ^ A name for a local variable, e.g. one that is
                          --   bound by a type alias.
    | -- | The index of a name in some environment
      --
      -- Before serializing names, they are converted to indices. The names
      -- themselves are kept in an environment or table that is serialized
      -- separately. This is to acommodate how GHC serializes its Names.
      LHRIndex Word
  deriving (Data, Eq, Generic, Ord)

-- | A name that is potentially unresolved.
data LHName
    = -- | In order to integrate the resolved names gradually, we keep the
      -- unresolved names.
      LHNResolved !LHResolvedName !Symbol
    | LHNUnresolved !LHNameSpace !Symbol
  deriving (Data, Generic)

-- | An Eq instance that ignores the Symbol in resolved names
instance Eq LHName where
  LHNResolved n0 _ == LHNResolved n1 _ = n0 == n1
  LHNUnresolved ns0 s0 == LHNUnresolved ns1 s1 = ns0 == ns1 && s0 == s1
  _ == _ = False

-- | An Ord instance that ignores the Symbol in resolved names
instance Ord LHName where
  compare (LHNResolved n0 _) (LHNResolved n1 _) = compare n0 n1
  compare (LHNUnresolved ns0 s0) (LHNUnresolved ns1 s1) =
    compare (ns0, s0) (ns1, s1)
  compare LHNResolved{} _ = LT
  compare LHNUnresolved{} _ = GT

-- | A Hashable instance that ignores the Symbol in resolved names
instance Hashable LHName where
  hashWithSalt s (LHNResolved n _) = hashWithSalt s n
  hashWithSalt s (LHNUnresolved ns sym) = s `hashWithSalt` ns `hashWithSalt` sym

data LHNameSpace
    = LHTcName
    | LHDataConName LHThisModuleNameFlag
    | LHVarName LHThisModuleNameFlag
    | LHLogicNameBinder
    | LHLogicName
  deriving (Data, Eq, Generic, Ord, Show)

instance B.Binary LHNameSpace
instance NFData LHNameSpace
instance Hashable LHNameSpace

-- | Whether the name should be looked up in the current module only or in any
-- module
data LHThisModuleNameFlag = LHThisModuleNameF | LHAnyModuleNameF
  deriving (Data, Eq, Generic, Ord, Show)

instance B.Binary LHThisModuleNameFlag
instance NFData LHThisModuleNameFlag
instance Hashable LHThisModuleNameFlag

instance Ord LogicName where
  compare (LogicName s1 m1 _) (LogicName s2 m2 _) =
    case compare s1 s2 of
      EQ -> GHC.stableModuleCmp m1 m2
      x -> x
  compare LogicName{} GeneratedLogicName{} = LT
  compare GeneratedLogicName{} LogicName{} = GT
  compare (GeneratedLogicName s1) (GeneratedLogicName s2) = compare s1 s2

instance Show LHName where
  showsPrec d n0 = showParen (d > app_prec) $ case n0 of
      LHNResolved n s ->
        showString "LHNResolved " .
        showsPrec (app_prec + 1) n .
        showSpace .
        showsPrec (app_prec + 1) s
      LHNUnresolved ns s ->
        showString "LHNUnresolved " .
        showsPrec (app_prec + 1) ns .
        showSpace .
        showsPrec (app_prec + 1) s
    where
      app_prec = 10

instance Show LHResolvedName where
  showsPrec d n0 = showParen (d > app_prec) $ case n0 of
      LHRGHC n1 -> showString "LHRGHC " . showString (GHC.showPprDebug n1)
      LHRLogic n1 -> showString "LHRLogic " . showsPrec (app_prec + 1) n1
      LHRLocal n1 -> showString "LHRLocal " . showsPrec (app_prec + 1) n1
      LHRIndex i -> showString "LHRIndex " . showsPrec (app_prec + 1) i
    where
      app_prec = 10

instance Show LogicName where
  showsPrec d n0 = showParen (d > app_prec) $ case n0 of
      LogicName s1 m mr ->
        showString "LogicName " .
        showsPrec (app_prec + 1) s1 .
        showSpace .
        showString (GHC.showPprDebug m) .
        showSpace .
        showsPrecMaybeName mr
      GeneratedLogicName s1 ->
        showString "GeneratedLogicName " .
        showsPrec (app_prec + 1) s1
    where
      app_prec = 10

      showsPrecMaybeName mr = case mr of
        Nothing -> showString "Nothing"
        Just n -> showParen True $ showString "Just " . showString (GHC.showPprDebug n)

instance NFData LHName
instance NFData LHResolvedName
instance NFData LogicName

instance Hashable LHResolvedName where
  hashWithSalt s (LHRLogic n) = s `hashWithSalt` (0::Int) `hashWithSalt` n
  hashWithSalt s (LHRGHC n) =
    s `hashWithSalt` (1::Int) `hashWithSalt` GHC.getKey (GHC.nameUnique n)
  hashWithSalt s (LHRLocal n) = s `hashWithSalt` (2::Int) `hashWithSalt` n
  hashWithSalt s (LHRIndex w) = s `hashWithSalt` (3::Int) `hashWithSalt` w

instance Hashable LogicName where
  hashWithSalt s (LogicName sym m _) =
        s `hashWithSalt` sym
          `hashWithSalt` GHC.moduleStableString m
  hashWithSalt s (GeneratedLogicName sym) =
        s `hashWithSalt` sym

instance B.Binary LHName
instance B.Binary LHResolvedName where
  get = do
    tag <- B.getWord8
    case tag of
      0 -> LHRLocal . fromString <$> B.get
      1 -> LHRIndex <$> B.get
      _ -> error "B.Binary: invalid tag for LHResolvedName"
  put (LHRLogic _n) = error "cannot serialize LHRLogic"
  put (LHRGHC _n) = error "cannot serialize LHRGHC"
  put (LHRLocal s) = B.putWord8 0 >> B.put (symbolString s)
  put (LHRIndex n) = B.putWord8 1 >> B.put n

instance GHC.Binary LHResolvedName where
  get bh = do
    tag <- GHC.getByte bh
    case tag of
      0 -> LHRLogic <$> GHC.get bh
      1 -> LHRGHC <$> GHC.get bh
      2 -> LHRLocal . fromString <$> GHC.get bh
      _ -> error "GHC.Binary: invalid tag for LHResolvedName"
  put_ bh (LHRLogic n) = GHC.putByte bh 0 >> GHC.put_ bh n
  put_ bh (LHRGHC n) = GHC.putByte bh 1 >> GHC.put_ bh n
  put_ bh (LHRLocal n) = GHC.putByte bh 2 >> GHC.put_ bh (symbolString n)
  put_ _bh (LHRIndex _n) = error "GHC.Binary: cannot serialize LHRIndex"

instance GHC.Binary LogicName where
  get bh = do
    tag <- GHC.getByte bh
    case tag of
      0 -> LogicName . fromString <$> GHC.get bh <*> GHC.get bh <*> GHC.get bh
      1 -> GeneratedLogicName . fromString <$> GHC.get bh
      _ -> error "GHC.Binary: invalid tag for LogicName"
  put_ bh (LogicName s m r) = do
    GHC.putByte bh 0
    GHC.put_ bh (symbolString s) >> GHC.put_ bh m >> GHC.put_ bh r
  put_ bh (GeneratedLogicName s) = do
    GHC.putByte bh 1
    GHC.put_ bh (symbolString s)

instance PPrint LHName where
  pprintTidy _ = pprint . getLHNameSymbol

makeResolvedLHName :: LHResolvedName -> Symbol -> LHName
makeResolvedLHName = LHNResolved

makeGHCLHName :: GHC.Name -> Symbol -> LHName
makeGHCLHName n s = makeResolvedLHName (LHRGHC n) s

makeGHCLHNameFromId :: GHC.Id -> LHName
makeGHCLHNameFromId x =
    let n = case GHC.idDetails x of
              GHC.DataConWrapId dc -> GHC.getName dc
              GHC.DataConWorkId dc -> GHC.getName dc
              _ -> GHC.getName x
     in makeGHCLHName n (symbol n)

makeLocalLHName :: Symbol -> LHName
makeLocalLHName s = LHNResolved (LHRLocal s) s

makeLogicLHName :: Symbol -> GHC.Module -> Maybe GHC.Name -> LHName
makeLogicLHName s m r = LHNResolved (LHRLogic (LogicName s m r)) s

makeGeneratedLogicLHName :: Symbol -> LHName
makeGeneratedLogicLHName s = LHNResolved (LHRLogic (GeneratedLogicName s)) s

makeGHCLHNameLocated :: (GHC.NamedThing a, Symbolic a) => a -> Located LHName
makeGHCLHNameLocated x =
    makeGHCLHName (GHC.getName x) (symbol x) <$ locNamedThing x

makeGHCLHNameLocatedFromId :: GHC.Id -> Located LHName
makeGHCLHNameLocatedFromId x =
    case GHC.idDetails x of
      GHC.DataConWrapId dc -> makeGHCLHNameLocated (GHC.getName dc)
      GHC.DataConWorkId dc -> makeGHCLHNameLocated (GHC.getName dc)
      _ -> makeGHCLHNameLocated x

makeUnresolvedLHName :: LHNameSpace -> Symbol -> LHName
makeUnresolvedLHName = LHNUnresolved

-- | Get the unresolved Symbol from an LHName.
getLHNameSymbol :: LHName -> Symbol
getLHNameSymbol (LHNResolved _ s) = s
getLHNameSymbol (LHNUnresolved _ s) = s

-- | Get the resolved Symbol from an LHName.
getLHNameResolved :: HasCallStack => LHName -> LHResolvedName
getLHNameResolved (LHNResolved n _) = n
getLHNameResolved n@LHNUnresolved{} = error $ "getLHNameResolved: unresolved name: " ++ show n

getLHGHCName :: LHName -> Maybe GHC.Name
getLHGHCName (LHNResolved (LHRGHC n) _) = Just n
getLHGHCName _ = Nothing

mapLHNames :: Data a => (LHName -> LHName) -> a -> a
mapLHNames f = go
  where
    go :: Data a => a -> a
    go = gmapT (go `extT` f)

mapMLocLHNames :: forall m a. (Data a, Monad m) => (Located LHName -> m (Located LHName)) -> a -> m a
mapMLocLHNames f = go
  where
    go :: forall b. Data b => b -> m b
    go = gmapM (go `extM` f)

updateLHNameSymbol :: (Symbol -> Symbol) -> LHName -> LHName
updateLHNameSymbol f (LHNResolved n s) = LHNResolved n (f s)
updateLHNameSymbol f (LHNUnresolved n s) = LHNUnresolved n (f s)

-- | Converts resolved names to symbols.
--
-- One important postcondition of this function is that the symbol for reflected
-- names must match exactly the symbol for the corresponding Haskell function.
-- Otherwise, LH would fail to link the two at various places where it is needed.
lhNameToResolvedSymbol :: LHName -> Symbol
lhNameToResolvedSymbol (LHNResolved (LHRLogic (LogicName s om mReflectionOf)) _) =
    let m = maybe om GHC.nameModule mReflectionOf
        msymbol = Text.pack $ GHC.moduleNameString $ GHC.moduleName m
     in symbol $ mconcat [msymbol, ".", symbolText s]
        {-
        TODO: Adding a prefix for the unit would allow LH to deal with
              -XPackageImports. This prefix should be added here and in
              the Symbolic instance of Name.
        munique =
          Text.dropEnd 2 $ -- Remove padding of two characters "=="
          Base64.extractBase64 $
          Base64.encodeBase64 $
          ByteString.toStrict $
          Builder.toLazyByteString $
          Builder.int32BE $
          fromIntegral $
          hash $
          GHC.unitIdString $
          GHC.moduleUnitId m
     in symbol $ mconcat ["u", munique, "##", msymbol, ".", symbolText s]
          -}
lhNameToResolvedSymbol (LHNResolved (LHRLogic (GeneratedLogicName s)) _) = s
lhNameToResolvedSymbol (LHNResolved (LHRLocal s) _) = s
lhNameToResolvedSymbol (LHNResolved (LHRGHC n) _) = symbol n
lhNameToResolvedSymbol n = error $ "lhNameToResolvedSymbol: unexpected name: " ++ show n

lhNameToUnqualifiedSymbol :: HasCallStack => LHName -> Symbol
lhNameToUnqualifiedSymbol (LHNResolved (LHRLogic (LogicName s _ _)) _) = s
lhNameToUnqualifiedSymbol (LHNResolved (LHRLogic (GeneratedLogicName s)) _) = s
lhNameToUnqualifiedSymbol (LHNResolved (LHRLocal s) _) = s
lhNameToUnqualifiedSymbol (LHNResolved (LHRGHC n) _) = symbol $ GHC.getOccString n
lhNameToUnqualifiedSymbol n = error $ "lhNameToUnqualifiedSymbol: unexpected name: " ++ show n

-- | Creates a name in the logic namespace for the given Haskell name.
reflectLHName :: HasCallStack => GHC.Module -> LHName -> LHName
reflectLHName thisModule (LHNResolved (LHRGHC n) _) = reflectGHCName thisModule n
reflectLHName _ n = error $ "not a GHC Name: " ++ show n

-- | Creates a name in the logic namespace for the given Haskell name.
reflectGHCName :: GHC.Module -> GHC.Name -> LHName
reflectGHCName thisModule n =
    LHNResolved
      (LHRLogic
        (LogicName
          (symbol (GHC.occNameString $ GHC.nameOccName n))
          thisModule
          (Just n)
        )
      )
      (symbol n)

maybeReflectedLHName :: LHName -> Maybe GHC.Name
maybeReflectedLHName (LHNResolved (LHRLogic (LogicName _ _ m)) _) = m
maybeReflectedLHName _ = Nothing
