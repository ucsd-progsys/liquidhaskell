{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Haskell.Liquid.GHC.Plugin.Types
    ( SpecComment(..)

    -- * Dealing with specs and their dependencies
    , LiquidLib
    , mkLiquidLib
    , libTarget
    , libDeps
    , allDeps
    , addLibDependencies

    -- * Caching specs into interfaces
    , CachedSpec
    , toCached
    , cachedSpecStableModuleId
    , cachedSpecModule
    , fromCached

    -- * Merging specs together
    , TargetSpec
    , ClientSpec
    , CompanionSpec
    , LiquidSpec
    , downcastSpec
    , mkTargetSpec
    , mkClientSpec
    , mkCompanionSpec
    , mergeTargetWithClient
    , mergeTargetWithCompanion

    -- * Acquiring and manipulating data from the typechecking phase
    , TcData
    , tcAllImports
    , tcQualifiedImports
    , tcResolvedNames
    , mkTcData

    -- * Wrapper type to talk about unoptimised things
    , Unoptimised(fromUnoptimised)
    , toUnoptimised

    , debugShowModule
    ) where

import           Data.Binary                             as B
import           Data.Data                                ( Data )
import           Data.Foldable
import           Text.Parsec                              ( SourcePos )
import           Outputable                        hiding ( (<>) )
import           GHC.Generics                      hiding ( moduleName )
import qualified Language.Haskell.Liquid.GHC.GhcMonadLike as GhcMonadLike
import           GHC                                      ( LImportDecl
                                                          , GhcRn
                                                          , Name
                                                          , TyThing
                                                          )
import           HscTypes                                 ( ModGuts )
import           TcRnTypes                                ( TcGblEnv(tcg_rn_imports) )
import           UniqFM
import           Module                                   ( ModuleName
                                                          , UnitId
                                                          , Module(..)
                                                          , moduleName
                                                          , moduleUnitId
                                                          , unitIdString
                                                          , moduleNameString
                                                          , mkModuleName
                                                          , stringToUnitId
                                                          , moduleStableString
                                                          , stableModuleCmp
                                                          )

import           Data.Map                                 ( Map )
import qualified Data.Map.Strict                         as M
import qualified Data.HashSet        as HS
import           Data.HashSet                             ( HashSet )
import           Data.Hashable
import qualified Data.Text.Lazy                          as TL

import           Language.Fixpoint.Types.Spans
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Specs      ( QImports )
import           Language.Haskell.Liquid.Measure          ( BareSpec, Spec(..) )
import qualified Language.Haskell.Liquid.GHC.Interface   as LH
import           Language.Fixpoint.Types.Names            ( Symbol )


import qualified Data.List as L


data LiquidLib = LiquidLib
  {  llTarget :: BareSpec
  -- ^ The target 'BareSpec'.
  ,  llDeps   :: HashSet CachedSpec
  -- ^ The specs which were necessary to produce the target 'BareSpec'.
  } deriving (Show, Generic)

instance B.Binary LiquidLib

-- | Creates a new 'LiquidLib' with no dependencies.
mkLiquidLib :: LiquidSpec ClientSpec -> LiquidLib
mkLiquidLib (MkClientSpec s) = LiquidLib s mempty

-- | Adds a set of dependencies to the input 'LiquidLib'.
addLibDependencies :: HashSet CachedSpec -> LiquidLib -> LiquidLib
addLibDependencies deps lib = lib { llDeps = deps <> (llDeps lib) }

-- | Returns the target 'BareSpec' of this 'LiquidLib'.
libTarget :: LiquidLib -> BareSpec
libTarget = llTarget

-- | Returns all the dependencies of this 'LiquidLib'.
libDeps :: LiquidLib -> HashSet CachedSpec
libDeps = llDeps

-- | Extracts all the dependencies from a collection of 'LiquidLib's.
allDeps :: Foldable f => f LiquidLib -> HashSet CachedSpec
allDeps = foldl' (\acc lib -> acc <> llDeps lib) mempty

-- | A newtype wrapper around a 'Module' which:
--
-- * Allows a 'Module' to be serialised (i.e. it has a 'Binary' instance)
-- * It tries to use stable comparison and equality under the hood.
--
newtype StableModule = StableModule Module

instance Ord StableModule where
  (StableModule m1) `compare` (StableModule m2) = stableModuleCmp m1 m2

instance Eq StableModule where
  (StableModule m1) == (StableModule m2) = (m1 `stableModuleCmp` m2) == EQ

instance Show StableModule where
    show (StableModule mdl) = "Stable" ++ debugShowModule mdl

-- | Converts a 'Module' into a 'StableModule'.
toStableModule :: Module -> StableModule
toStableModule = StableModule

instance Binary StableModule where
    put (StableModule mdl) = do
      put (unitIdString . moduleUnitId $ mdl)
      put (moduleNameString . moduleName $ mdl)

    get = do
      uidStr <- get
      mnStr  <- get
      pure $ StableModule (Module (stringToUnitId uidStr) (mkModuleName mnStr))


-- | A cached spec which can be serialised into an interface.
--
-- /INVARIANT/: A 'CachedSpec' has temination-checking disabled 
-- (i.e. 'noTerm' is called on the inner 'BareSpec').
data CachedSpec = CachedSpec StableModule BareSpec deriving (Show, Generic)

instance Binary CachedSpec

instance Eq CachedSpec where
    (CachedSpec id1 _) == (CachedSpec id2 _) = id1 == id2

instance Hashable CachedSpec where
    hashWithSalt s (CachedSpec (StableModule mdl) _) = 
      hashWithSalt s (moduleStableString mdl)

-- | Converts the input 'BareSpec' into a 'CachedSpec', inforcing the invariant that termination checking
-- needs to be disabled as this is now considered safe to use for \"clients\".
toCached :: Module -> BareSpec -> CachedSpec
toCached mdl bareSpec = CachedSpec (toStableModule mdl) (LH.noTerm bareSpec)

cachedSpecStableModuleId :: CachedSpec -> String
cachedSpecStableModuleId (CachedSpec (StableModule m) _) = moduleStableString m

cachedSpecModule :: CachedSpec -> Module
cachedSpecModule (CachedSpec (StableModule m) _) = m

fromCached :: CachedSpec -> (ModName, BareSpec)
fromCached (CachedSpec (StableModule mdl) s) = (ModName SrcImport (moduleName mdl), s)

--
-- Merging specs together.
--

-- | Checks if the two input declarations are equal, by checking not only that their value
-- is the same, but also that they are declared exactly in the same place.
sameSig :: (LocSymbol, LocBareType) -> (LocSymbol, LocBareType) -> Bool
sameSig (ls1, lbt1) (ls2, lbt2) =
  (ls1 == ls2 ) && (srcSpan lbt1 == srcSpan lbt2)

---
--- A Liquid spec and its (many) flavours
---

data TargetSpec
data ClientSpec
data CompanionSpec

data LiquidSpec t where
    MkTargetSpec    :: BareSpec -> LiquidSpec TargetSpec
    MkClientSpec    :: BareSpec -> LiquidSpec ClientSpec
    MkCompanionSpec :: BareSpec -> LiquidSpec CompanionSpec

deriving instance Show (LiquidSpec TargetSpec)
deriving instance Show (LiquidSpec ClientSpec)
deriving instance Show (LiquidSpec CompanionSpec)

mkTargetSpec :: BareSpec -> LiquidSpec TargetSpec
mkTargetSpec = MkTargetSpec

mkClientSpec :: BareSpec -> LiquidSpec ClientSpec
mkClientSpec = MkClientSpec

mkCompanionSpec :: BareSpec -> LiquidSpec CompanionSpec
mkCompanionSpec = MkCompanionSpec

downcastSpec :: LiquidSpec t -> BareSpec
downcastSpec = \case
  MkTargetSpec s    -> s
  MkClientSpec s    -> s
  MkCompanionSpec s -> s

-- | Merges a 'TargetSpec' with its 'CompanionSpec'. Here duplicates are not checked as it's
-- user's responsibility to make sure there are no duplicates between the in-module annotations and the
-- companion spec.
mergeTargetWithCompanion :: LiquidSpec TargetSpec -> LiquidSpec CompanionSpec -> LiquidSpec TargetSpec
mergeTargetWithCompanion (MkTargetSpec s1) (MkCompanionSpec s2) = MkTargetSpec (s1 <> s2)

-- | Merges a 'TargetSpec' with its 'ClientSpec'. Here we need to be careful when it comes to signatures,
-- because the 'ClientSpec' will "lift" the definition by \"pointing\" to the source line of the actual
-- Haskell function definition, whereas the 'ClientSpec' would refer only to the source line of the LH
-- annotation, and this could lead to \"multiple declarations\" false positives.
-- On top of this, we disable the termination checks for the resulting spec, as this will be stored inside
-- as an interface's annotation.
mergeTargetWithClient :: LiquidSpec TargetSpec -> LiquidSpec ClientSpec -> LiquidSpec ClientSpec
mergeTargetWithClient (MkTargetSpec s1) (MkClientSpec s2) = MkClientSpec . LH.noTerm $
  (s1 <> s2) { 
      sigs       = L.deleteFirstsBy (\a b -> fst a == fst b) (sigs s1) (asmSigs s2)
    , aliases    = L.nubBy (\a b -> srcSpan a == srcSpan b) (aliases  s1 <> aliases s2)
    , ealiases   = L.nubBy (\a b -> srcSpan a == srcSpan b) (ealiases s1 <> ealiases s2)
    , qualifiers = L.nub (qualifiers s1 <> qualifiers s2)
    , dataDecls  = L.nub (dataDecls s1 <> dataDecls s2)
    }

-- | Just a small wrapper around the 'SourcePos' and the text fragment of a LH spec comment.
newtype SpecComment =
    SpecComment (SourcePos, String)
    deriving Data

newtype Unoptimised a = Unoptimised { fromUnoptimised :: a }

toUnoptimised :: a -> Unoptimised a
toUnoptimised = Unoptimised

-- | Data which can be \"safely\" passed to the \"Core\" stage of the pipeline.
-- The notion of \"safely\" here is a bit vague: things like imports are somewhat
-- guaranteed not to change, but things like identifiers might, so they shouldn't
-- land here.
data TcData = TcData {
    tcAllImports       :: HS.HashSet Symbol
  , tcQualifiedImports :: QImports
  , tcResolvedNames    :: [(Name, Maybe TyThing)]
  }

instance Outputable TcData where
    ppr (TcData{..}) = 
          text "TcData { imports  = " <+> text (show $ HS.toList tcAllImports)
      <+> text "       , qImports = " <+> text (show tcQualifiedImports)
      <+> text "       , names    = " <+> ppr tcResolvedNames
      <+> text " }"

-- | Constructs a 'TcData' out of a 'TcGblEnv'.
mkTcData :: GhcMonadLike.TypecheckedModule -> [(Name, Maybe TyThing)] -> TcData
mkTcData tcModule resolvedNames = TcData {
    tcAllImports       = LH.allImports       (GhcMonadLike.tm_renamed_source tcModule)
  , tcQualifiedImports = LH.qualifiedImports (GhcMonadLike.tm_renamed_source tcModule)
  , tcResolvedNames    = resolvedNames
  }

debugShowModule :: Module -> String
debugShowModule m = showSDocUnsafe $
                     text "Module { unitId = " <+> ppr (moduleUnitId m)
                 <+> text ", name = " <+> ppr (moduleName m) 
                 <+> text " }"
