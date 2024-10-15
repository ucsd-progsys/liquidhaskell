{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
module Language.Haskell.Liquid.Types.Names
  ( lenLocSymbol
  , anyTypeSymbol
  , functionComposisionSymbol
  , selfSymbol
  , LogicName (..)
  , LHResolvedName (..)
  , LHName
  , LHNameSpace (..)
  , makeResolvedLHName
  , getLHNameResolved
  , getLHNameSymbol
  , makeUnresolvedLHName
  , mapLHNames
  ) where

import Control.DeepSeq
import qualified Data.Binary as B
import Data.Data (Data, gmapT)
import Data.Generics (extT)
import Data.Hashable
import GHC.Generics
import GHC.Stack
import Language.Fixpoint.Types
import qualified Liquid.GHC.API as GHC

-- RJ: Please add docs
lenLocSymbol :: Located Symbol
lenLocSymbol = dummyLoc $ symbol ("autolen" :: String)

anyTypeSymbol :: Symbol
anyTypeSymbol = symbol ("GHC.Prim.Any" :: String)


--  defined in include/GHC/Base.hs
functionComposisionSymbol :: Symbol
functionComposisionSymbol = symbol ("GHC.Internal.Base.." :: String)


selfSymbol :: Symbol
selfSymbol = symbol ("liquid_internal_this" :: String)

-- | A name for an entity that does not exist in Haskell
--
-- For instance, this can be used to represent predicate aliases
-- or uninterpreted functions.
data LogicName = LogicName
    { lnSymbol :: !Symbol
    , lnModule :: !GHC.Module
    }
  deriving (Data, Eq, Generic)

-- | A name whose procedence is known.
data LHResolvedName
    = LHRLogic !LogicName
    | LHRGHC !GHC.Name    -- ^ A name for an entity that exists in Haskell
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
  deriving (Data, Eq, Generic, Ord)

data LHNameSpace
    = LHTcName
  deriving (Data, Eq, Generic, Ord)

instance B.Binary LHNameSpace
instance NFData LHNameSpace
instance Hashable LHNameSpace

instance Ord LogicName where
  compare (LogicName s1 m1) (LogicName s2 m2) =
    case compare s1 s2 of
      EQ -> GHC.stableModuleCmp m1 m2
      x -> x

instance Show LHName where
  show (LHNResolved _ s) = show s
  show (LHNUnresolved _ s) = show s

instance NFData LHName
instance NFData LHResolvedName
instance NFData LogicName

instance Hashable LHResolvedName where
  hashWithSalt s (LHRLogic n) = s `hashWithSalt` (0::Int) `hashWithSalt` n
  hashWithSalt s (LHRGHC n) =
    s `hashWithSalt` (1::Int) `hashWithSalt` GHC.getKey (GHC.nameUnique n)
  hashWithSalt s (LHRIndex w) = s `hashWithSalt` (2::Int) `hashWithSalt` w

instance Hashable LHName
instance Hashable LogicName where
  hashWithSalt s (LogicName sym m) =
        s `hashWithSalt` sym
          `hashWithSalt` GHC.moduleStableString m

instance B.Binary LHName
instance B.Binary LHResolvedName where
  get = LHRIndex <$> B.get
  put (LHRLogic _n) = error "cannot serialize LHRLogic"
  put (LHRGHC _n) = error "cannot serialize LHRGHC"
  put (LHRIndex n) = B.put n

makeResolvedLHName :: LHResolvedName -> Symbol -> LHName
makeResolvedLHName = LHNResolved

makeUnresolvedLHName :: LHNameSpace -> Symbol -> LHName
makeUnresolvedLHName = LHNUnresolved

-- | Get the unresolved Symbol from an LHName.
getLHNameSymbol :: LHName -> Symbol
getLHNameSymbol (LHNResolved _ s) = s
getLHNameSymbol (LHNUnresolved _ s) = s

-- | Get the unresolved Symbol from an LHName.
getLHNameResolved :: HasCallStack => LHName -> LHResolvedName
getLHNameResolved (LHNResolved n _) = n
getLHNameResolved n@LHNUnresolved{} = error $ "getLHNameResolved: unresolved name: " ++ show n

mapLHNames :: Data a => (LHName -> LHName) -> a -> a
mapLHNames f = go
  where
    go :: Data a => a -> a
    go = gmapT (go `extT` f)
