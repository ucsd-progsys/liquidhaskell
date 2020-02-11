{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes   #-}

module Language.Haskell.Liquid.GHC.Plugin.SpecFinder
    ( findRelevantSpecs
    , SpecFinderResult(..)
    , SearchLocation(..)
    , TargetModule(..)
    -- * Temporary internals
    , findBaseSpecs
    ) where

import           Language.Haskell.Liquid.Measure          ( BareSpec )
import           Language.Haskell.Liquid.GHC.GhcMonadLike as GhcMonadLike ( GhcMonadLike
                                                                          , getModSummary
                                                                          )
import           Language.Haskell.Liquid.GHC.Plugin.Util  ( pluginAbort, deserialiseBareSpecs )
import           Language.Haskell.Liquid.GHC.Plugin.Types
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.GHC.Interface

import qualified Outputable                              as O
import           GHC
import           HscTypes
import           CoreMonad                                ( getDynFlags )

import qualified Data.HashSet                            as HS
import qualified Data.Map.Strict                         as M
import qualified Data.List                               as L
import           Data.Foldable

import           Control.Monad
import           Control.Monad.Trans                      ( lift )
import           Control.Monad.Trans.Maybe

type SpecFinder m = GhcMonadLike m => SpecEnv -> Module -> MaybeT m SpecFinderResult

-- | The result of searching for a spec.
data SpecFinderResult = 
    SpecNotFound ModuleName
  | ExternalSpecFound ModuleName SearchLocation CachedSpec
  -- ^ Only a single spec was found. This is the typical case for interface loading.
  | BaseSpecsFound ModuleName SearchLocation [CachedSpec]
  -- The spec was found and was fetched together with any required specs the module requires.

-- | The module we are currently compiling/processing as part of the Plugin infrastructure.
newtype TargetModule = TargetModule { getTargetModule :: Module }

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
                                 , loadFromAnnotations eps currentEnv currentModule
                                 ]

      -- The 'baseSpecFinder' needs to go last and triggers disk I/O in trying to fetch spec files from
      -- the filesystem, if the configuration has changed or if the cache is empty.
      let baseSpecFinder =
            if | fetchFromDisk ->
                 [loadSpecFromDisk cfg (getTargetModule target) (resetBaseSpecs currentEnv) currentModule]
               | baseCacheEmpty currentEnv ->
                 [loadSpecFromDisk cfg (getTargetModule target) currentEnv currentModule]
               | otherwise      ->
                 [lookupCachedBaseSpec currentEnv currentModule]

      res <- runMaybeT (asum $ externalSpecsFinders <> baseSpecFinder)
      case res of
        Nothing         -> pure (False, currentEnv, SpecNotFound (moduleName currentModule) : acc)
        Just specResult -> do
          let env' = case specResult of
                       ExternalSpecFound _originalMod _location spec ->
                         insertExternalSpec currentModule spec currentEnv
                       BaseSpecsFound _originalMod _location specs ->
                         replaceBaseSpecs specs currentEnv
                       SpecNotFound _ -> currentEnv
          pure (False, env', specResult : acc)

-- | Try to load the spec from the 'SpecEnv'.
lookupCachedExternalSpec :: SpecFinder m
lookupCachedExternalSpec specEnv thisModule = do
  b <- MaybeT $ pure $ M.lookup thisModule (externalSpecs specEnv)
  pure $ ExternalSpecFound (moduleName thisModule) SpecEnvLocation b

lookupCachedBaseSpec :: SpecFinder m
lookupCachedBaseSpec specEnv thisModule = do
  guard $ (not $ L.null (baseSpecs specEnv))
  pure  $ BaseSpecsFound (moduleName thisModule) SpecEnvLocation (baseSpecs specEnv)

-- | Load a spec by trying to parse the relevant \".spec\" file from the filesystem.
loadSpecFromDisk :: Config -> Module -> SpecFinder m
loadSpecFromDisk cfg targetModule _specEnv thisModule = do
  modSummary <- lift $ GhcMonadLike.getModSummary (moduleName targetModule)
  bareSpecs  <- lift $ findBaseSpecs cfg modSummary
  case bareSpecs of
    []         -> MaybeT $ pure Nothing
    specs      -> pure $ BaseSpecsFound (moduleName thisModule) DiskLocation (map toCached specs)


findBaseSpecs :: GhcMonadLike m 
              => Config 
              -> ModSummary 
              -> m [(ModName, BareSpec)]
findBaseSpecs cfg modSum =
  let paths = HS.fromList $ idirs cfg ++ importPaths (ms_hspp_opts modSum)
  in findAndParseSpecFiles cfg paths modSum mempty

-- | Load a spec by trying to parse the relevant \".spec\" file from the filesystem.
loadFromAnnotations :: ExternalPackageState -> SpecFinder m
loadFromAnnotations eps _specEnv thisModule = do
  let bareSpecs = deserialiseBareSpecs thisModule eps
  case bareSpecs of
    []         -> MaybeT $ pure Nothing
    [bareSpec] -> 
      let cachedSpec = CachedSpec (ModName SrcImport (moduleName thisModule)) bareSpec
      in pure $ ExternalSpecFound (moduleName thisModule) InterfaceLocation cachedSpec
    specs      -> do
      dynFlags <- lift getDynFlags
      let errMsg = O.text "More than one spec file found for" 
             O.<+> O.ppr thisModule O.<+> O.text ":"
             O.<+> (O.vcat $ map (O.text . show) specs)
      lift $ pluginAbort dynFlags errMsg
