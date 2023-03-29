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
    , getTyThingsFromWiredInModules
    ) where

import           Liquid.GHC.GhcMonadLike as GhcMonadLike ( GhcMonadLike
                                                                          , lookupModSummary
                                                                          , askHscEnv
                                                                          )
import           Language.Haskell.Liquid.GHC.Plugin.Util  ( pluginAbort, deserialiseLiquidLib )
import           Language.Haskell.Liquid.GHC.Plugin.Types
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Specs     hiding (Spec)
import qualified Language.Haskell.Liquid.Measure         as Measure
import qualified Language.Haskell.Liquid.Misc            as Misc
import           Language.Haskell.Liquid.Parse            ( specSpecificationP )
import           Language.Fixpoint.Utils.Files            ( Ext(Spec), withExt )
import           Language.Fixpoint.Types.Names            ( Symbol, symbolString )

import           Optics
import           Paths_liquidhaskell (getDataFileName)
import qualified Liquid.GHC.API         as O
import           Liquid.GHC.API         as GHC
import           Liquid.GHC.Interface (getTyThingsFromExternalModules, parseSpecFile)

import           Data.Bifunctor
import qualified Data.HashMap.Strict as HashMap
import           Data.IORef
import           Data.Maybe
import qualified Data.Set as Set

import           Control.Exception
import           Control.Monad                            ( forM )
import           Control.Monad.Trans                      ( lift )
import           Control.Monad.Trans.Maybe

import           Text.Megaparsec.Error
import           System.Directory (listDirectory)
import           System.FilePath ((</>))
import           System.IO.Unsafe (unsafePerformIO)

type SpecFinder m = GhcMonadLike m => Module -> MaybeT m SpecFinderResult

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
findRelevantSpecs :: forall m. GhcMonadLike m
                  => ExternalPackageState
                  -> HomePackageTable
                  -> [Module]
                  -- ^ Any relevant module fetched during dependency-discovery.
                  -> m [SpecFinderResult]
findRelevantSpecs eps hpt mods = do
    rs <- liftIO $ findWiredInSpecs mods
    (++ rs) <$> foldlM loadRelevantSpec mempty mods
  where

    loadRelevantSpec :: [SpecFinderResult] -> Module -> m [SpecFinderResult]
    loadRelevantSpec !acc currentModule = do
      res <- runMaybeT $ lookupInterfaceAnnotations eps hpt currentModule
      pure $ case res of
        Nothing         -> SpecNotFound currentModule : acc
        Just specResult -> specResult : acc


-- | Yields the spec files from the boot libraries corresponding to
-- any modules mentioned in the given list.
findWiredInSpecs :: [Module] -> IO [SpecFinderResult]
findWiredInSpecs mods = fmap catMaybes $ forM mods $ \m ->
    let u = unitString (moduleUnit m)
        ms = moduleNameString (moduleName m)
     in case findSpecFile u ms (knownPackages wiredInSpecsEnv) of
          Nothing -> return Nothing
          Just specFile -> do
            (_, spec) <- parseSpecFile specFile
            importSpecs <- parseSpecFileTree u (imports spec)
            let liquidLib = mkLiquidLibFromDeps m spec importSpecs
            return $ Just $ LibFound m DiskLocation liquidLib
  where
    -- | Finds a spec file given the unit name, the module name, and the
    -- list of known packages.
    findSpecFile :: String -> String -> [String] -> Maybe FilePath
    findSpecFile _u _ms [] = Nothing
    findSpecFile u ms (p:ps) = do
      let specFile = p </> ms <> ".spec"
      if p == u && Set.member specFile (knownSpecs wiredInSpecsEnv) then
        Just $ knownPackagesDir wiredInSpecsEnv </> specFile
      else
        findSpecFile u ms ps

    -- | Yields the list of transitively imported modules from a given unit name
    -- and list of module names (as symbols).
    parseSpecFileTree :: String -> [Symbol] -> IO [(ModName, Measure.BareSpec)]
    parseSpecFileTree u importSyms = do
      let symbolToSpecFile s =
            knownPackagesDir wiredInSpecsEnv </> u </> symbolString s <> ".spec"
      rs <- mapM (readWiredInSpec wiredInSpecsEnv . symbolToSpecFile) importSyms
      fmap concat $ forM rs $ \r@(_, spec) -> do
        importSpecs <- parseSpecFileTree u (imports spec)
        return (r : importSpecs)

    mkLiquidLibFromDeps
      :: Module -> Measure.BareSpec -> [(ModName, Measure.BareSpec)] -> LiquidLib
    mkLiquidLibFromDeps m spec importSpecs =
      let depsList = [ ( mkStableModule (moduleUnitId m) (getModName mn)
                       , view liftedSpecGetter sp
                       )
                     | (mn, sp) <- importSpecs
                     ]
          deps = TargetDependencies $ HashMap.fromList depsList
       in
          addLibDependencies deps $ mkLiquidLib (view liftedSpecGetter spec)

-- | Information about wired in packages
data WiredInSpecsEnv = WiredInSpecsEnv
       { -- | Directory containing the spec files of the known packages
         knownPackagesDir :: FilePath
         -- | Names of known packages
       , knownPackages :: [String]
         -- | Paths to spec files relative to the knownPackagesDir
       , knownSpecs :: Set.Set FilePath
         -- | Specs loaded so far
       , knownSpecsCache :: IORef (HashMap.HashMap FilePath (ModName,Measure.BareSpec))
       }

{-# NOINLINE wiredInSpecsEnv #-}
wiredInSpecsEnv :: WiredInSpecsEnv
wiredInSpecsEnv = unsafePerformIO $ do
    knownPackagesDir <- getDataFileName "include/known-packages"
    knownPackages <- listDirectory knownPackagesDir
    knownSpecs <- fmap (Set.fromList . concat) $
      forM knownPackages $ \p ->
        fmap (p </>) <$> listDirectory (knownPackagesDir </> p)
    knownSpecsCache <- newIORef mempty

    return $ WiredInSpecsEnv
      knownPackagesDir
      knownPackages
      knownSpecs
      knownSpecsCache

getTyThingsFromWiredInModules
  :: GhcMonadLike m => TargetDependencies -> m [TyThing]
getTyThingsFromWiredInModules dependencies =
    getTyThingsFromExternalModules $
      filter ((`elem` knownPackages wiredInSpecsEnv) . unitString . moduleUnit) $
      map unStableModule $ HashMap.keys $ getDependencies dependencies

-- | Reads a spec file updating the cache in the given environment
readWiredInSpec :: WiredInSpecsEnv -> FilePath -> IO (ModName, Measure.BareSpec)
readWiredInSpec env f = do
    c0 <- readIORef (knownSpecsCache env)
    case HashMap.lookup f c0 of
      Nothing -> do
        r <- parseSpecFile f
        atomicModifyIORef (knownSpecsCache env) $ \c ->
          (HashMap.insert f r c, r)
      Just r ->
        return r


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
    Left peb -> do
      dynFlags <- lift getDynFlags
      let errMsg = O.text "Error when parsing "
             O.<+> O.text (specFile file) O.<+> O.text ":"
             O.<+> O.text (errorBundlePretty peb)
      lift $ pluginAbort (O.showSDoc dynFlags errMsg)
    Right (_, spec) -> do
      let bareSpec = view bareSpecIso spec
      pure $ SpecFound thisModule DiskLocation bareSpec
  where
    specFile :: FilePath -> FilePath
    specFile fp = withExt fp Spec

-- | Returns a list of 'StableModule's which can be filtered out of the dependency list, because they are
-- selectively \"toggled\" on and off by the LiquidHaskell's configuration, which granularity can be
-- /per module/.
configToRedundantDependencies :: forall m. GhcMonadLike m => Config -> m [StableModule]
configToRedundantDependencies cfg = do
  env <- askHscEnv
  catMaybes <$> mapM (lookupModule' env . first ($ cfg)) configSensitiveDependencies
  where
    lookupModule' :: HscEnv -> (Bool, ModuleName) -> m (Maybe StableModule)
    lookupModule' env (fetchModule, modName)
      | fetchModule = liftIO $ lookupLiquidBaseModule env modName
      | otherwise   = pure Nothing

    lookupLiquidBaseModule :: HscEnv -> ModuleName -> IO (Maybe StableModule)
    lookupLiquidBaseModule env mn = do
      res <- liftIO $ findExposedPackageModule env mn (Just "liquid-base")
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
    (not . totalityCheck, mkModuleName "Liquid.Prelude.Totality")
  , (not . linear, mkModuleName "Liquid.Prelude.NotReal")
  , (linear, mkModuleName "Liquid.Prelude.Real")
  ]
