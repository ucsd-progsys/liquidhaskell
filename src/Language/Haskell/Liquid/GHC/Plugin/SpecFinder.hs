{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes   #-}

module Language.Haskell.Liquid.GHC.Plugin.SpecFinder
    ( findRelevantSpecs
    , findCompanionSpec
    , SpecFinderResult(..)
    , SearchLocation(..)
    , TargetModule(..)
    ) where

import           Language.Haskell.Liquid.Measure          ( BareSpec )
import           Language.Haskell.Liquid.GHC.GhcMonadLike as GhcMonadLike ( GhcMonadLike
                                                                          , getModSummary
                                                                          , lookupModSummary
                                                                          )
import           Language.Haskell.Liquid.GHC.Plugin.Util  ( pluginAbort, deserialiseBareSpecs )
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
import           Data.Foldable
import           Data.Maybe

import           Control.Exception
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans                      ( lift )
import           Control.Monad.Trans.Maybe

--import Debug.Trace

type SpecFinder m = GhcMonadLike m => SpecEnv -> Module -> MaybeT m SpecFinderResult

-- | The result of searching for a spec.
data SpecFinderResult = 
    SpecNotFound Module
  | ExternalSpecFound ModuleName SearchLocation CachedSpec
  -- ^ Only a single spec was found. This is the typical case for interface loading.
  | BaseSpecsFound ModuleName SearchLocation [CachedSpec]
  -- The spec was found and was fetched together with any required specs the module requires.
  | CompanionSpecFound ModuleName SearchLocation CachedSpec
  -- The spec was found alongside the compiled module, on the filesystem.

-- | The module we are currently compiling/processing as part of the Plugin infrastructure.
newtype TargetModule = TargetModule { getTargetModule :: Module }

data SearchLocation =
    InterfaceLocation
  -- ^ The spec was loaded from the annotations of an interface.
  | SpecEnvLocation
  -- ^ The spec was loaded from the cached 'SpecEnv'.
  | DiskLocation
  -- ^ The spec was loaded from disk (e.g. 'Prelude.spec' or similar)
  | IncludeDirLocation
  -- ^ The spec was loaded from the `include` directory in the LH root project.
  deriving Show

-- | Load any relevant spec in the input 'SpecEnv', by updating it. The update will happen only if necessary,
-- i.e. if the spec is not already present.
findRelevantSpecs :: forall m. GhcMonadLike m 
                  => (Config, Bool)
                  -> ExternalPackageState
                  -> SpecEnv 
                  -> TargetModule
                  -> [Module]
                  -> m (SpecEnv, [SpecFinderResult])
findRelevantSpecs (cfg, configChanged) eps specEnv target mods = do
  (_, specEnv', res) <- foldlM loadRelevantSpec (configChanged, specEnv, mempty) mods
  pure (specEnv', res)
  where
    baseCacheEmpty :: SpecEnv -> Bool
    baseCacheEmpty env = L.null (baseSpecs env)

    loadRelevantSpec :: (Bool, SpecEnv, [SpecFinderResult]) -> Module -> m (Bool, SpecEnv, [SpecFinderResult])
    loadRelevantSpec (fetchFromDisk, currentEnv, !acc) currentModule = do
      let externalSpecsFinders = [ lookupCachedExternalSpec currentEnv currentModule
                                 , lookupInterfaceAnnotations eps currentEnv currentModule
                                 --, lookupCompanionSpec currentEnv currentModule
                                 ]

      -- The 'baseSpecFinder' needs to go last and triggers disk I/O in trying to fetch spec files from
      -- the filesystem, if the configuration has changed or if the cache is empty.
      --let baseSpecFinder =
      --      if | fetchFromDisk ->
      --           [loadSpecFromDisk cfg (getTargetModule target) (resetBaseSpecs currentEnv) currentModule]
      --         | baseCacheEmpty currentEnv ->
      --           [loadSpecFromDisk cfg (getTargetModule target) currentEnv currentModule]
      --         | otherwise      ->
      --           [lookupCachedBaseSpec currentEnv currentModule]

      res <- runMaybeT (asum $ externalSpecsFinders {- <> baseSpecFinder -})
      case res of
        Nothing         -> pure (False, currentEnv, SpecNotFound currentModule : acc)
        Just specResult -> do
          let env' = case specResult of
                       ExternalSpecFound _originalMod SpecEnvLocation _spec ->
                         currentEnv  -- If this was already in the map, do not override it.
                       ExternalSpecFound _originalMod _location spec ->
                         insertExternalSpec currentModule spec currentEnv
                       CompanionSpecFound _originalMod _location spec ->
                         insertExternalSpec currentModule spec currentEnv
                       BaseSpecsFound _originalMod _location specs ->
                         replaceBaseSpecs specs currentEnv
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
  b <- MaybeT $ pure $ M.lookup thisModule (externalSpecs specEnv)
  pure $ ExternalSpecFound (moduleName thisModule) SpecEnvLocation b

lookupCachedBaseSpec :: SpecFinder m
lookupCachedBaseSpec specEnv thisModule = do
  guard (isJust $ find (\cs -> getModName (fst $ fromCached cs) == moduleName thisModule) (baseSpecs specEnv))
  pure  $ BaseSpecsFound (moduleName thisModule) SpecEnvLocation (baseSpecs specEnv)

-- | Load a spec by trying to parse the relevant \".spec\" file from the filesystem.
loadSpecFromDisk :: Config -> Module -> SpecFinder m
loadSpecFromDisk cfg targetModule _specEnv thisModule = do
  modSummary <- lift $ GhcMonadLike.getModSummary (moduleName targetModule)
  bareSpecs  <- lift $ findBaseSpecs cfg modSummary
  case bareSpecs of
    []         -> MaybeT $ pure Nothing
    specs      -> do
      guard (isJust $ find (\(n,_) -> getModName n == moduleName thisModule) specs)
      pure $ BaseSpecsFound (moduleName thisModule) IncludeDirLocation (map toCached specs)

findBaseSpecs :: GhcMonadLike m 
              => Config 
              -> ModSummary 
              -> m [(ModName, BareSpec)]
findBaseSpecs cfg modSum =
  let paths = HS.fromList $ idirs cfg ++ importPaths (ms_hspp_opts modSum)
  in findAndParseSpecFiles cfg paths modSum mempty

-- | Load a spec by trying to parse the relevant \".spec\" file from the filesystem.
lookupInterfaceAnnotations :: ExternalPackageState -> SpecFinder m
lookupInterfaceAnnotations eps _specEnv thisModule = do
  let bareSpecs = deserialiseBareSpecs thisModule eps
  case bareSpecs of
    []         -> MaybeT $ pure Nothing
    [bareSpec] -> 
      let cachedSpec = toCached (ModName SrcImport (moduleName thisModule), bareSpec)
      in pure $ ExternalSpecFound (moduleName thisModule) InterfaceLocation cachedSpec
    specs      -> do
      dynFlags <- lift getDynFlags
      let errMsg = O.text "More than one spec file found for" 
             O.<+> O.ppr thisModule O.<+> O.text ":"
             O.<+> (O.vcat $ map (O.text . show) specs)
      lift $ pluginAbort dynFlags errMsg

-- | If this module has a \"companion\" '.spec' file sitting next to it, this 'SpecFinder'
-- will try loading it.
lookupCompanionSpec :: SpecFinder m
lookupCompanionSpec _specEnv thisModule = do

  modSummary <- MaybeT $ GhcMonadLike.lookupModSummary (moduleName thisModule)
  file       <- MaybeT $ pure (ml_hs_file . ms_location $ modSummary)
  spec       <- MaybeT $ do
    mbSpecContent <- liftIO $ try (Misc.sayReadFile (specFile file))
    case mbSpecContent of
      Left (_e :: SomeException) -> pure Nothing
      Right raw -> pure $ either (const Nothing) (Just . id) (specSpecificationP (specFile file) raw)

  pure $ CompanionSpecFound (moduleName thisModule) DiskLocation (toCached spec)
  where
    specFile :: FilePath -> FilePath
    specFile fp = withExt fp Spec
