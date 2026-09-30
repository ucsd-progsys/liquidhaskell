{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Haskell.Liquid.GHC.Plugin.Types
    ( SpecComment(..)

    -- * Dealing with specs and their dependencies
    , LiquidLib
    , mkLiquidLib
    , mkSpecComment
    , libTarget
    , libDeps
    , SpecReference(..)
    , addLibDependencies

    -- * Carrying data across stages of the compilation pipeline
    , PipelineData(..)

    -- * Acquiring and manipulating data from the typechecking phase
    ) where

import           Data.Binary                             as B
import           Data.Data                               ( Data )
import           GHC.Generics                      hiding ( moduleName )

import           Language.Haskell.Liquid.Parse (BPspec)
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.GHC.Plugin.Iface (PayloadId)
import           Liquid.GHC.API         as GHC
import           Language.Haskell.Liquid.GHC.Misc (realSrcLocSourcePos)
import           Language.Fixpoint.Types.Spans            ( SourcePos, dummyPos )


data LiquidLib = LiquidLib
  {  llTarget :: LiftedSpec
  -- ^ The target /LiftedSpec/.
  ,  llDeps   :: [SpecReference]
  -- ^ The exact dependency selection used to check the target. This is a flat
  -- list of references, so configuration-sensitive exclusions are preserved
  -- without embedding the dependencies' specification bodies again.
  } deriving (Show, Data, Generic)

instance B.Binary LiquidLib

data SpecReference = SpecReference
  { specModule :: StableModule
  , specFingerprint :: PayloadId
  } deriving (Eq, Ord, Show, Data, Generic)

instance B.Binary SpecReference

-- | Creates a new 'LiquidLib' with no dependencies.
mkLiquidLib :: LiftedSpec -> LiquidLib
mkLiquidLib s = LiquidLib s mempty

-- | Adds a set of dependencies to the input 'LiquidLib'.
addLibDependencies :: [SpecReference] -> LiquidLib -> LiquidLib
addLibDependencies deps lib = lib { llDeps = deps <> llDeps lib }

-- | Returns the target 'LiftedSpec' of this 'LiquidLib'.
libTarget :: LiquidLib -> LiftedSpec
libTarget = llTarget

-- | Returns all the dependencies of this 'LiquidLib'.
libDeps :: LiquidLib -> [SpecReference]
libDeps = llDeps

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
  , pdSpecComments :: [BPspec]
  }
