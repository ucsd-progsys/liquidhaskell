{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes   #-}

module Language.Haskell.Liquid.GHC.Plugin.SpecFinder
    ( findRelevantSpecs
    , findCompanionSpec
    , SpecFinderResult(..)
    , SearchLocation(..)
    , configToRedundantDependencies
    ) where

import qualified Language.Haskell.Liquid.GHC.Plugin.Util as Util
import           Language.Haskell.Liquid.GHC.Plugin.Types
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Specs     hiding (Spec)
import qualified Language.Haskell.Liquid.Misc            as Misc
import           Language.Haskell.Liquid.Parse            ( specSpecificationP )
import           Language.Fixpoint.Utils.Files            ( Ext(Spec), withExt )

import qualified Liquid.GHC.API         as O
import           Liquid.GHC.API         as GHC

import           Data.Bifunctor
import qualified Data.Char
import           Data.IORef
import           Data.Maybe

import           Control.Exception
import           Control.Monad                            ( foldM )
import           Control.Monad.Trans                      ( lift )
import           Control.Monad.Trans.Maybe

import           Text.Megaparsec.Error

type SpecFinder m = Module -> MaybeT IO SpecFinderResult

-- | The result of searching for a spec.
data SpecFinderResult = 
    SpecNotFound Module
  | SpecFound Module SearchLocation BareSpec
  | LibFound  Module SearchLocation LiquidLib

data SearchLocation =
    InterfaceLocation
  -- ^ The spec was loaded from the annotations of an interface.
  | DiskLocation
  -- ^ The spec was loaded from disk (e.g. 'Prelude.spec' or similar)
  deriving Show

-- | Load any relevant spec for the input list of 'Module's, by querying both the 'ExternalPackageState'
-- and the 'HomePackageTable'.
--
-- Specs come from the interface files of the given modules or their matching
-- _LHAssumptions modules. A module @M@ only matches with a module named
-- @M_LHAssumptions@.
--
-- Assumptions are taken from _LHAssumptions modules only if the interface
-- file of the matching module contains no spec.
findRelevantSpecs :: [String] -- ^ Package to exclude for loading LHAssumptions
                  -> HscEnv
                  -> [Module]
                  -- ^ Any relevant module fetched during dependency-discovery.
                  -> TcM [SpecFinderResult]
findRelevantSpecs lhAssmPkgExcludes hscEnv mods = do
    eps <- liftIO $ readIORef (euc_eps $ ue_eps $ hsc_unit_env hscEnv)
    foldM (loadRelevantSpec eps) mempty mods
  where

    loadRelevantSpec :: ExternalPackageState -> [SpecFinderResult] -> Module -> TcM [SpecFinderResult]
    loadRelevantSpec eps !acc currentModule = do
      res <- liftIO $ runMaybeT $
        lookupInterfaceAnnotations eps (ue_hpt $ hsc_unit_env hscEnv) currentModule
      case res of
        Nothing         -> do
          mAssm <- loadModuleLHAssumptionsIfAny currentModule
          return $ fromMaybe (SpecNotFound currentModule) mAssm : acc
        Just specResult ->
          return (specResult : acc)

    loadModuleLHAssumptionsIfAny m | isImportExcluded m = return Nothing
                                   | otherwise = do
      let assumptionsModName = assumptionsModuleName m
      -- loadInterface might mutate the EPS if the module is
      -- not already loaded
      res <- liftIO $ findImportedModule hscEnv assumptionsModName NoPkgQual
      case res of
        Found _ assumptionsMod -> do
          _ <- initIfaceTcRn $ loadInterface "liquidhaskell assumptions" assumptionsMod ImportBySystem
          -- read the EPS again
          eps2 <- liftIO $ readIORef (euc_eps $ ue_eps $ hsc_unit_env hscEnv)
          -- now look up the assumptions
          liftIO $ runMaybeT $ lookupInterfaceAnnotationsEPS eps2 assumptionsMod
        FoundMultiple{} -> failWithTc $ mkTcRnUnknownMessage $ mkPlainError [] $
                             missingInterfaceErrorDiagnostic (initIfaceMessageOpts $ hsc_dflags hscEnv) $
                             cannotFindModule hscEnv assumptionsModName res
        _ -> return Nothing

    isImportExcluded m =
      let s = takeWhile Data.Char.isAlphaNum $ unitString (moduleUnit m)
       in elem s lhAssmPkgExcludes

    assumptionsModuleName m =
      mkModuleNameFS $ moduleNameFS (moduleName m) <> "_LHAssumptions"

-- | If this module has a \"companion\" '.spec' file sitting next to it, this 'SpecFinder'
-- will try loading it.
findCompanionSpec :: HscEnv -> Module -> IO SpecFinderResult
findCompanionSpec hscEnv m = do
  res <- runMaybeT $ lookupCompanionSpec hscEnv m
  case res of
    Nothing -> pure $ SpecNotFound m
    Just s  -> pure s

-- | Load a spec by trying to parse the relevant \".spec\" file from the filesystem.
lookupInterfaceAnnotations :: ExternalPackageState -> HomePackageTable -> SpecFinder m
lookupInterfaceAnnotations eps hpt thisModule = do
  lib <- MaybeT $ pure $ Util.deserialiseLiquidLib thisModule eps hpt
  pure $ LibFound thisModule InterfaceLocation lib

lookupInterfaceAnnotationsEPS :: ExternalPackageState -> SpecFinder m
lookupInterfaceAnnotationsEPS eps thisModule = do
  lib <- MaybeT $ pure $ Util.deserialiseLiquidLibFromEPS thisModule eps
  pure $ LibFound thisModule InterfaceLocation lib

-- | If this module has a \"companion\" '.spec' file sitting next to it, this 'SpecFinder'
-- will try loading it.
lookupCompanionSpec :: HscEnv -> SpecFinder m
lookupCompanionSpec hscEnv thisModule = do

  modSummary <- MaybeT $ pure $ lookupModSummary hscEnv (moduleName thisModule)
  file       <- MaybeT $ pure (ml_hs_file . ms_location $ modSummary)
  parsed     <- MaybeT $ do
    mbSpecContent <- try (Misc.sayReadFile (specFile file))
    case mbSpecContent of
      Left (_e :: SomeException) -> pure Nothing
      Right raw -> pure $ Just $ specSpecificationP (specFile file) raw

  case parsed of
    Left peb -> do
      let errMsg = O.text "Error when parsing "
             O.<+> O.text (specFile file) O.<+> O.text ":"
             O.<+> O.text (errorBundlePretty peb)
      lift $ Util.pluginAbort (O.showSDoc (hsc_dflags hscEnv) errMsg)
    Right (_, spec) -> do
      let bareSpec = toBareSpec spec
      pure $ SpecFound thisModule DiskLocation bareSpec
  where
    specFile :: FilePath -> FilePath
    specFile fp = withExt fp Spec

-- | Returns a list of 'StableModule's which can be filtered out of the dependency list, because they are
-- selectively \"toggled\" on and off by the LiquidHaskell's configuration, which granularity can be
-- /per module/.
configToRedundantDependencies :: HscEnv -> Config -> IO [StableModule]
configToRedundantDependencies env cfg = do
  catMaybes <$> mapM (lookupModule' . first ($ cfg)) configSensitiveDependencies
  where
    lookupModule' :: (Bool, ModuleName) -> IO (Maybe StableModule)
    lookupModule' (fetchModule, modName)
      | fetchModule = lookupLiquidBaseModule modName
      | otherwise   = pure Nothing

    lookupLiquidBaseModule :: ModuleName -> IO (Maybe StableModule)
    lookupLiquidBaseModule mn = do
      res <- findImportedModule env mn (renamePkgQual (hsc_unit_env env) mn (Just "liquidhaskell"))
      case res of
        Found _ mdl -> pure $ Just (toStableModule mdl)
        _           -> pure Nothing

-- | Static associative map of the 'ModuleName' that needs to be filtered from the final 'TargetDependencies'
-- due to some particular configuration options.
--
-- Modify this map to add any extra special case. Remember that the semantic is not which module will be
-- /added/, but rather which one will be /removed/ from the final list of dependencies.
--
configSensitiveDependencies :: [(Config -> Bool, ModuleName)]
configSensitiveDependencies = [
    (not . totalityCheck, mkModuleName "Liquid.Prelude.Totality_LHAssumptions")
  , (linear, mkModuleName "Liquid.Prelude.Real_LHAssumptions")
  ]
