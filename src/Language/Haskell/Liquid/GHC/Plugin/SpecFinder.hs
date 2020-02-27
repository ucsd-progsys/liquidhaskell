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

import           Language.Haskell.Liquid.Measure          ( BareSpec )
import           Language.Haskell.Liquid.GHC.GhcMonadLike as GhcMonadLike ( GhcMonadLike
                                                                          , getModSummary
                                                                          , lookupModSummary
                                                                          )
import           Language.Haskell.Liquid.GHC.Plugin.Util  ( pluginAbort, deserialiseLiquidLib )
import           Language.Haskell.Liquid.GHC.Plugin.Types
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.GHC.Interface
import qualified Language.Haskell.Liquid.Misc            as Misc
import           Language.Haskell.Liquid.Parse            ( specSpecificationP )
import           Language.Fixpoint.Utils.Files            ( Ext(Spec), withExt )

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

type SpecFinder m = GhcMonadLike m => SpecEnv -> Module -> MaybeT m SpecFinderResult

-- | The result of searching for a spec.
data SpecFinderResult = 
    SpecNotFound Module
  | SpecFound Module SearchLocation LiquidLib

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
                  -> SpecEnv 
                  -> [Module]
                  -> m (SpecEnv, [SpecFinderResult])
findRelevantSpecs (cfg, configChanged) eps hpt specEnv mods = do
  (_, specEnv', res) <- foldlM loadRelevantSpec (configChanged, specEnv, mempty) mods
  pure (specEnv', res)
  where

    loadRelevantSpec :: (Bool, SpecEnv, [SpecFinderResult]) -> Module -> m (Bool, SpecEnv, [SpecFinderResult])
    loadRelevantSpec (cfgChanged, currentEnv, !acc) currentModule = do
      let externalSpecsFinders = [ -- lookupCachedExternalSpec currentEnv currentModule
                                 lookupInterfaceAnnotations eps hpt currentEnv currentModule
                                 ]

      res <- runMaybeT $ asum externalSpecsFinders
      case res of
        Nothing         -> pure (False, currentEnv, SpecNotFound currentModule : acc)
        Just specResult -> do
          let env' = case specResult of
                       SpecFound _originalMod SpecEnvLocation _lib ->
                         currentEnv  -- If this was already in the map, do not override it.
                       SpecFound _originalMod _location lib ->
                         currentEnv & insertExternalSpec currentModule (toCached currentModule $ libTarget lib)
                                    . flip (foldl' (\acc s -> insertExternalSpec (cachedSpecModule s) s acc)) (libDeps lib)
                       SpecNotFound _ -> currentEnv
          pure (False, env', specResult : acc)

-- | If this module has a \"companion\" '.spec' file sitting next to it, this 'SpecFinder'
-- will try loading it.
findCompanionSpec :: GhcMonadLike m => SpecEnv -> Module -> m SpecFinderResult
findCompanionSpec env m = do
  res <- runMaybeT $ lookupCompanionSpec env m
  case res of
    Nothing -> pure $ SpecNotFound m
    Just s  -> pure s

-- | Try to load the spec from the 'SpecEnv'.
lookupCachedExternalSpec :: SpecFinder m
lookupCachedExternalSpec specEnv thisModule = do
  b <- MaybeT $ pure $ lookupExternalSpec thisModule specEnv
  pure $ SpecFound thisModule SpecEnvLocation (mkLiquidLib . snd $ fromCached b)

-- | Load a spec by trying to parse the relevant \".spec\" file from the filesystem.
lookupInterfaceAnnotations :: ExternalPackageState -> HomePackageTable -> SpecFinder m
lookupInterfaceAnnotations eps hpt _specEnv thisModule = do
  lib <- MaybeT $ pure $ deserialiseLiquidLib thisModule eps hpt
  pure $ SpecFound thisModule InterfaceLocation lib

-- | If this module has a \"companion\" '.spec' file sitting next to it, this 'SpecFinder'
-- will try loading it.
lookupCompanionSpec :: SpecFinder m
lookupCompanionSpec _specEnv thisModule = do

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
    Right spec -> pure $ SpecFound thisModule DiskLocation (mkLiquidLib . snd $ spec)
  where
    specFile :: FilePath -> FilePath
    specFile fp = withExt fp Spec
