{-# LANGUAGE DeriveGeneric #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Liquid.GHC.API.StableModule (
    StableModule
  -- * Constructing a 'StableModule'
  , mkStableModule
  -- * Converting a 'StableModule' into a standard 'Module'
  , unStableModule
  -- * Utility functions
  , toStableModule
  , renderModule
  ) where

import qualified GHC
import qualified GHC.Unit.Types as GHC
import qualified GHC.Unit.Module as GHC
import           Data.Hashable
import           GHC.Generics            hiding (to, moduleName)
import           Data.Binary

-- | A newtype wrapper around a 'Module' which:
--
-- * Allows a 'Module' to be serialised (i.e. it has a 'Binary' instance)
-- * It tries to use stable comparison and equality under the hood.
--
newtype StableModule =
  StableModule { unStableModule :: GHC.Module }
  deriving Generic

-- | Converts a 'Module' into a 'StableModule'.
toStableModule :: GHC.Module -> StableModule
toStableModule = StableModule

moduleUnitId :: GHC.Module -> GHC.UnitId
moduleUnitId = GHC.toUnitId . GHC.moduleUnit

renderModule :: GHC.Module -> String
renderModule m =    "Module { unitId = " <> (GHC.unitIdString . moduleUnitId $ m)
                 <> ", name = " <> GHC.moduleNameString (GHC.moduleName m)
                 <> " }"

-- These two orphans originally lived inside module 'Language.Haskell.Liquid.Types.Types'.
instance Hashable GHC.ModuleName where
  hashWithSalt i = hashWithSalt i . GHC.moduleNameString

instance Hashable StableModule where
  hashWithSalt s (StableModule mdl) = hashWithSalt s (GHC.moduleStableString mdl)

instance Ord StableModule where
  (StableModule m1) `compare` (StableModule m2) = GHC.stableModuleCmp m1 m2

instance Eq StableModule where
  (StableModule m1) == (StableModule m2) = (m1 `GHC.stableModuleCmp` m2) == EQ

instance Show StableModule where
    show (StableModule mdl) = "Stable" ++ renderModule mdl

instance Binary StableModule where

    put (StableModule mdl) = do
      put (GHC.unitIdString . moduleUnitId $ mdl)
      put (GHC.moduleNameString . GHC.moduleName $ mdl)

    get = do
      uidStr <- get
      mkStableModule (GHC.stringToUnitId uidStr) . GHC.mkModuleName <$> get

--
-- Compat shim layer
--

-- | Creates a new 'StableModule' out of a 'ModuleName' and a 'UnitId'.
mkStableModule :: GHC.UnitId -> GHC.ModuleName -> StableModule
mkStableModule uid modName =
  let realUnit = GHC.RealUnit $ GHC.Definite uid
  in StableModule (GHC.Module realUnit modName)
