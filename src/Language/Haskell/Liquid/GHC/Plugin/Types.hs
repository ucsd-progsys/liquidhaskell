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
    , InputSpec
    , CompanionSpec
    , LiquidSpec
    , downcastSpec
    , mkInputSpec
    , mkCompanionSpec
    , mergeInputWithCompanion

    -- * Acquiring and manipulating data from the typechecking phase
    , TcData
    , tcAllImports
    , tcQualifiedImports
    , tcResolvedNames
    , tcAvailableTyCons
    , tcAvailableVars
    , mkTcData

    -- * Wrapper type to talk about unoptimised things
    , Unoptimised(fromUnoptimised)
    , toUnoptimised
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
                                                          , TyCon
                                                          )
import           Var                                      ( Var )
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
import           Language.Haskell.Liquid.Types.Types hiding (BareSpec(..), Spec(..))
import           Language.Haskell.Liquid.Types.SpecDesign
import           Language.Haskell.Liquid.Types.Specs      ( QImports )
import qualified Language.Haskell.Liquid.GHC.Interface   as LH
import           Language.Fixpoint.Types.Names            ( Symbol )


import qualified Data.List as L


data LiquidLib = LiquidLib
  {  llTarget :: LiftedSpec
  -- ^ The target /LiftedSpec/.
  ,  llDeps   :: TargetDependencies
  -- ^ The specs which were necessary to produce the target 'BareSpec'.
  } deriving (Show, Generic)

instance B.Binary LiquidLib

-- | Creates a new 'LiquidLib' with no dependencies.
mkLiquidLib :: LiftedSpec -> LiquidLib
mkLiquidLib s = LiquidLib s mempty

-- | Adds a set of dependencies to the input 'LiquidLib'.
addLibDependencies :: TargetDependencies -> LiquidLib -> LiquidLib
addLibDependencies deps lib = lib { llDeps = deps <> (llDeps lib) }

-- | Returns the target 'LiftedSpec' of this 'LiquidLib'.
libTarget :: LiquidLib -> LiftedSpec
libTarget = llTarget

-- | Returns all the dependencies of this 'LiquidLib'.
libDeps :: LiquidLib -> TargetDependencies
libDeps = llDeps

-- | Extracts all the dependencies from a collection of 'LiquidLib's.
allDeps :: Foldable f => f LiquidLib -> TargetDependencies
allDeps = foldl' (\acc lib -> acc <> llDeps lib) mempty

-- | A cached spec which can be serialised into an interface.
data CachedSpec = CachedSpec StableModule LiftedSpec deriving (Show, Generic)

instance Binary CachedSpec

instance Eq CachedSpec where
    (CachedSpec id1 _) == (CachedSpec id2 _) = id1 == id2

instance Hashable CachedSpec where
    hashWithSalt s (CachedSpec (StableModule mdl) _) = 
      hashWithSalt s (moduleStableString mdl)

-- | Converts the input 'BareSpec' into a 'CachedSpec', inforcing the invariant that termination checking
-- needs to be disabled as this is now considered safe to use for \"clients\".
toCached :: Module -> LiftedSpec -> CachedSpec
toCached mdl liftedSpec = CachedSpec (toStableModule mdl) liftedSpec

cachedSpecStableModuleId :: CachedSpec -> String
cachedSpecStableModuleId (CachedSpec (StableModule m) _) = moduleStableString m

cachedSpecModule :: CachedSpec -> Module
cachedSpecModule (CachedSpec (StableModule m) _) = m

fromCached :: CachedSpec -> (StableModule, LiftedSpec)
fromCached (CachedSpec sm s) = (sm, s)

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

data InputSpec
data CompanionSpec

data LiquidSpec t where
    MkInputSpec     :: BareSpec   -> LiquidSpec InputSpec
    MkCompanionSpec :: BareSpec   -> LiquidSpec CompanionSpec

deriving instance Show (LiquidSpec InputSpec)
deriving instance Show (LiquidSpec CompanionSpec)

mkInputSpec :: BareSpec -> LiquidSpec InputSpec
mkInputSpec = MkInputSpec

mkCompanionSpec :: BareSpec -> LiquidSpec CompanionSpec
mkCompanionSpec = MkCompanionSpec

downcastSpec :: LiquidSpec t -> BareSpec
downcastSpec = \case
  MkInputSpec s    -> s
  MkCompanionSpec s -> s

-- | Merges a 'InputSpec' with its 'CompanionSpec'. Here duplicates are not checked as it's
-- user's responsibility to make sure there are no duplicates between the in-module annotations and the
-- companion spec.
mergeInputWithCompanion :: LiquidSpec InputSpec -> LiquidSpec CompanionSpec -> LiquidSpec InputSpec
mergeInputWithCompanion (MkInputSpec s1) (MkCompanionSpec s2) = MkInputSpec (s1 <> s2)

{-
-- | Merges a 'InputSpec' with its 'ClientSpec'. Here we need to be careful when it comes to signatures,
-- because the 'ClientSpec' will "lift" the definition by \"pointing\" to the source line of the actual
-- Haskell function definition, whereas the 'ClientSpec' would refer only to the source line of the LH
-- annotation, and this could lead to \"multiple declarations\" false positives.
-- On top of this, we disable the termination checks for the resulting spec, as this will be stored inside
-- as an interface's annotation.
mergeInputWithClient :: LiquidSpec InputSpec -> LiquidSpec ClientSpec -> LiquidSpec ClientSpec
mergeInputWithClient (MkInputSpec s1) (MkClientSpec s2) = MkClientSpec . LH.noTerm $
  (s1 <> s2) { 
      sigs       = L.deleteFirstsBy (\a b -> fst a == fst b) (sigs s1) (asmSigs s2)
    , aliases    = L.nubBy (\a b -> srcSpan a == srcSpan b) (aliases  s1 <> aliases s2)
    , ealiases   = L.nubBy (\a b -> srcSpan a == srcSpan b) (ealiases s1 <> ealiases s2)
    , qualifiers = L.nub (qualifiers s1 <> qualifiers s2)
    , dataDecls  = L.nub (dataDecls s1 <> dataDecls s2)
    }
-}

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
  , tcAvailableTyCons  :: [GHC.TyCon]
  -- ^ Sometimes we might be in a situation where we have \"wrapper\" modules that
  -- simply re-exports everything from the original module, and therefore when LH
  -- tries to resolve the GHC identifier associated to a data constructor in scope
  -- (from the call to 'lookupTyThings') we might not be able to find a match because
  -- the 'mg_tcs' for the input 'ModGuts' is empty (because the type constructor are not
  -- defined in the /wrapper/ module, but rather in the /wrapped/ module itself). This is
  -- why we look at the 'ModGuts' 's 'AvailInfo' to extract any re-exported 'TyCon' out of that.
  , tcAvailableVars    :: [Var]
  -- ^ Ditto as for 'reflectedTyCons', but for identifiers.
  }

instance Outputable TcData where
    ppr (TcData{..}) = 
          text "TcData { imports     = " <+> text (show $ HS.toList tcAllImports)
      <+> text "       , qImports    = " <+> text (show tcQualifiedImports)
      <+> text "       , names       = " <+> ppr tcResolvedNames
      <+> text "       , availTyCons = " <+> ppr tcAvailableTyCons
      <+> text " }"

-- | Constructs a 'TcData' out of a 'TcGblEnv'.
mkTcData :: GhcMonadLike.TypecheckedModule 
         -> [(Name, Maybe TyThing)] 
         -> [TyCon]
         -> [Var]
         -> TcData
mkTcData tcModule resolvedNames availTyCons availVars = TcData {
    tcAllImports       = LH.allImports       (GhcMonadLike.tm_renamed_source tcModule)
  , tcQualifiedImports = LH.qualifiedImports (GhcMonadLike.tm_renamed_source tcModule)
  , tcResolvedNames    = resolvedNames
  , tcAvailableTyCons  = availTyCons
  , tcAvailableVars    = availVars
  }
