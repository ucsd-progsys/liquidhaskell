{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Haskell.Liquid.GHC.Plugin.Types
    ( SpecComment(..)

    -- * Dealing with specs and their dependencies
    , LiquidLib
    , mkLiquidLib
    , mkSpecComment
    , libTarget
    , libDeps
    , allDeps
    , addLibDependencies

    -- * Carrying data across stages of the compilation pipeline
    , PipelineData(..)

    -- * Acquiring and manipulating data from the typechecking phase
    , TcData
    , tcAllImports
    , tcQualifiedImports
    , tcResolvedNames
    , tcAvailableTyCons
    , tcAvailableVars
    , mkTcData
    ) where

import           Data.Binary                             as B
import           Data.Foldable
import           GHC.Generics                      hiding ( moduleName )

import qualified Data.HashSet        as HS

import           Language.Haskell.Liquid.Types.Specs
import           Liquid.GHC.API         as GHC
import qualified Language.Haskell.Liquid.GHC.Interface   as LH
import           Language.Haskell.Liquid.GHC.Misc (realSrcLocSourcePos)
import           Language.Fixpoint.Types.Names            ( Symbol )
import           Language.Fixpoint.Types.Spans            ( SourcePos, dummyPos )


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
addLibDependencies deps lib = lib { llDeps = deps <> llDeps lib }

-- | Returns the target 'LiftedSpec' of this 'LiquidLib'.
libTarget :: LiquidLib -> LiftedSpec
libTarget = llTarget

-- | Returns all the dependencies of this 'LiquidLib'.
libDeps :: LiquidLib -> TargetDependencies
libDeps = llDeps

-- | Extracts all the dependencies from a collection of 'LiquidLib's.
allDeps :: Foldable f => f LiquidLib -> TargetDependencies
allDeps = foldl' (\acc lib -> acc <> llDeps lib) mempty

-- | Just a small wrapper around the 'SourcePos' and the text fragment of a LH spec comment.
newtype SpecComment =
    SpecComment (SourcePos, String)
    deriving Show

mkSpecComment :: (Maybe RealSrcLoc, String) -> SpecComment
mkSpecComment (m, s) = SpecComment (sourcePos m, s)
  where
    sourcePos Nothing = dummyPos "<no source information>"
    sourcePos (Just sp) = realSrcLocSourcePos sp

--
-- Passing data between stages of the pipeline
--
-- The plugin architecture doesn't provide a default system to \"thread\" data across stages of the
-- compilation pipeline, which means that plugin implementors have two choices:
--
-- 1. Serialise any data they want to carry around inside annotations, but this can be potentially costly;
-- 2. Pass data inside IORefs.

data PipelineData = PipelineData {
    pdUnoptimisedCore :: ModGuts
  , pdTcData :: TcData
  , pdSpecComments :: [SpecComment]
  }

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
mkTcData :: [LImportDecl GhcRn]
         -> [(Name, Maybe TyThing)]
         -> [TyCon]
         -> [Var]
         -> TcData
mkTcData imps resolvedNames availTyCons availVars = TcData {
    tcAllImports       = LH.allImports       imps
  , tcQualifiedImports = LH.qualifiedImports imps
  , tcResolvedNames    = resolvedNames
  , tcAvailableTyCons  = availTyCons
  , tcAvailableVars    = availVars
  }
