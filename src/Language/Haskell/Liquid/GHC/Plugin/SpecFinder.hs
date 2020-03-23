{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes   #-}

module Language.Haskell.Liquid.GHC.Plugin.SpecFinder
    ( findRelevantSpecs
    , findCompanionSpec
    , SpecFinderResult(..)
    , SearchLocation(..)
    ) where

import           Language.Haskell.Liquid.GHC.GhcMonadLike as GhcMonadLike ( GhcMonadLike
                                                                          , getModSummary
                                                                          , lookupModSummary
                                                                          )
import           Language.Haskell.Liquid.GHC.Plugin.Util  ( pluginAbort, deserialiseLiquidLib )
import           Language.Haskell.Liquid.GHC.Plugin.Types
import           Language.Haskell.Liquid.Types.Types (Config)
import           Language.Haskell.Liquid.Types.SpecDesign
import           Language.Haskell.Liquid.GHC.Interface
import qualified Language.Haskell.Liquid.Misc            as Misc
import           Language.Haskell.Liquid.Parse            ( specSpecificationP )
import           Language.Fixpoint.Utils.Files            ( Ext(Spec), withExt )

import           Optics
import qualified Outputable                              as O
import           GHC
import           HscTypes
import           CoreMonad                                ( getDynFlags )

import qualified Data.HashSet                            as HS
import qualified Data.Map.Strict                         as M
import qualified Data.List                               as L
import           Data.Function                            ( (&) )
import           Data.Foldable
import           Data.Maybe

import           Control.Exception
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans                      ( lift )
import           Control.Monad.Trans.Maybe

type SpecFinder m = GhcMonadLike m => Module -> MaybeT m SpecFinderResult

-- | The result of searching for a spec.
data SpecFinderResult = 
    SpecNotFound Module
  | SpecFound Module SearchLocation BareSpec
  | LibFound  Module SearchLocation LiquidLib

data SearchLocation =
    InterfaceLocation
  -- ^ The spec was loaded from the annotations of an interface.
  | SpecEnvLocation
  -- ^ The spec was loaded from the cached 'SpecEnv'.
  | DiskLocation
  -- ^ The spec was loaded from disk (e.g. 'Prelude.spec' or similar)
  deriving Show


-- | Load any relevant spec in the input 'SpecEnv', by updating it. The update will happen only if necessary,
-- i.e. if the spec is not already present.
findRelevantSpecs :: forall m. GhcMonadLike m 
                  => (Config, Bool)
                  -> ExternalPackageState
                  -> HomePackageTable
                  -> [Module]
                  -> m [SpecFinderResult]
findRelevantSpecs (cfg, configChanged) eps hpt mods = do
  (_, res) <- foldlM loadRelevantSpec (configChanged, mempty) mods
  pure res
  where

    loadRelevantSpec :: (Bool, [SpecFinderResult]) -> Module -> m (Bool, [SpecFinderResult])
    loadRelevantSpec (cfgChanged, !acc) currentModule = do
      res <- runMaybeT $ lookupInterfaceAnnotations eps hpt currentModule
      case res of
        Nothing         -> pure (False, SpecNotFound currentModule : acc)
        Just specResult -> pure (False, specResult : acc)

-- | If this module has a \"companion\" '.spec' file sitting next to it, this 'SpecFinder'
-- will try loading it.
findCompanionSpec :: GhcMonadLike m => Module -> m SpecFinderResult
findCompanionSpec m = do
  res <- runMaybeT $ lookupCompanionSpec m
  case res of
    Nothing -> pure $ SpecNotFound m
    Just s  -> pure s

-- | Load a spec by trying to parse the relevant \".spec\" file from the filesystem.
lookupInterfaceAnnotations :: ExternalPackageState -> HomePackageTable -> SpecFinder m
lookupInterfaceAnnotations eps hpt thisModule = do
  lib <- MaybeT $ pure $ deserialiseLiquidLib thisModule eps hpt
  pure $ LibFound thisModule InterfaceLocation lib

-- | If this module has a \"companion\" '.spec' file sitting next to it, this 'SpecFinder'
-- will try loading it.
lookupCompanionSpec :: SpecFinder m
lookupCompanionSpec thisModule = do

  modSummary <- MaybeT $ GhcMonadLike.lookupModSummary (moduleName thisModule)
  file       <- MaybeT $ pure (ml_hs_file . ms_location $ modSummary)
  parsed     <- MaybeT $ do
    mbSpecContent <- liftIO $ try (Misc.sayReadFile (specFile file))
    case mbSpecContent of
      Left (_e :: SomeException) -> pure Nothing
      Right raw -> pure $ Just $ specSpecificationP (specFile file) raw

  case parsed of
    Left parsingError -> do
      dynFlags <- lift getDynFlags
      let errMsg = O.text "Error when parsing " 
             O.<+> O.text (specFile file) O.<+> O.text ":"
             O.<+> O.text (show parsingError)
      lift $ pluginAbort dynFlags errMsg
    Right (_, spec) -> do
      let bareSpec = view bareSpecIso spec
      pure $ SpecFound thisModule DiskLocation bareSpec
  where
    specFile :: FilePath -> FilePath
    specFile fp = withExt fp Spec
