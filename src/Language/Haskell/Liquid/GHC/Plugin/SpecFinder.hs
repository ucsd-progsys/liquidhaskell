{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes   #-}

module Language.Haskell.Liquid.GHC.Plugin.SpecFinder
    ( findRelevantSpecs
    , SpecFinderResult(..)
    , SearchLocation(..)
    , TargetModule(..)
    -- * Temporary internals
    , findExternalSpecs
    ) where

import           Language.Haskell.Liquid.Measure          ( BareSpec )
import           Language.Haskell.Liquid.GHC.GhcMonadLike as GhcMonadLike ( GhcMonadLike
                                                                          , askHscEnv
                                                                          , getModSummary
                                                                          , lookupModule 
                                                                          )
import           Language.Haskell.Liquid.GHC.Plugin.Util  ( pluginAbort, deserialiseBareSpecs )
import           Language.Haskell.Liquid.GHC.Plugin.Types
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.GHC.Interface

import qualified Outputable                              as O
import           Module                                   ( Module, lookupModuleEnv, extendModuleEnv )
import           GHC
import           HscTypes
import           CoreMonad                                ( getDynFlags )
import           UniqFM

import qualified Data.HashSet                            as HS
import           Data.HashSet                             ( HashSet )
import qualified Data.Map.Strict                         as M
import           Data.Foldable

import           Control.Applicative                      ( (<|>) )
import           Control.Monad.Trans                      ( lift )
import           Control.Monad.Trans.Maybe

type SpecFinder m = GhcMonadLike m => SpecEnv -> Module -> MaybeT m SpecFinderResult

-- | The result of searching for a spec.
data SpecFinderResult = 
    SpecNotFound ModuleName
  | SpecFound  SearchLocation CachedSpec
  -- ^ Only a single spec was found. This is the typical case for interface loading.
  | MultipleSpecsFound SearchLocation (HashSet CachedSpec)
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
                  => Config 
                  -> ExternalPackageState
                  -> SpecEnv 
                  -> TargetModule
                  -> [Module]
                  -> m (SpecEnv, [SpecFinderResult])
findRelevantSpecs cfg eps specEnv target = foldlM loadRelevantSpec (specEnv, mempty)
  where
    loadRelevantSpec :: (SpecEnv, [SpecFinderResult]) -> Module -> m (SpecEnv, [SpecFinderResult])
    loadRelevantSpec (currentEnv, !acc) mod = do
      let finders = asum [ lookupCachedSpec currentEnv mod 
                         , loadFromAnnotations eps currentEnv mod
                         , loadSpecFromDisk cfg (getTargetModule target) currentEnv mod
                         ]
      res <- runMaybeT finders
      case res of
        Nothing         -> pure (currentEnv, SpecNotFound (moduleName mod) : acc)
        Just specResult -> do
          let env' = case specResult of
                       SpecFound location spec           ->
                         extendSpecEnv (moduleName mod) (HS.singleton spec) currentEnv
                       MultipleSpecsFound location specs ->
                         foldl' (\m el -> 
                           extendSpecEnv (cachedModuleName el) (HS.singleton el) m
                         ) currentEnv specs
          pure (env', specResult : acc)

-- | Try to load the spec from the 'SpecEnv'.
lookupCachedSpec :: SpecFinder m
lookupCachedSpec specEnv mod = do
  r <- MaybeT $ pure (M.lookup (moduleName mod) specEnv)
  case HS.toList r of
    [b] -> pure $ SpecFound SpecEnvLocation b
    bs  -> pure $ MultipleSpecsFound SpecEnvLocation (HS.fromList bs)

-- | Load a spec by trying to parse the relevant \".spec\" file from the filesystem.
loadSpecFromDisk :: Config -> Module -> SpecFinder m
loadSpecFromDisk cfg targetModule specEnv thisModule = do
  modSummary <- lift $ GhcMonadLike.getModSummary (moduleName targetModule)
  bareSpecs  <- lift $ findExternalSpecs cfg modSummary
  case bareSpecs of
    []         -> MaybeT $ pure Nothing
    [bareSpec] -> pure $ SpecFound DiskLocation (toCached bareSpec)
    specs      -> pure $ MultipleSpecsFound DiskLocation (HS.fromList $ map toCached specs)


findExternalSpecs :: GhcMonadLike m 
                  => Config 
                  -> ModSummary 
                  -> m [(ModName, BareSpec)]
findExternalSpecs cfg modSum =
  let paths = HS.fromList $ idirs cfg ++ importPaths (ms_hspp_opts modSum)
  in findAndParseSpecFiles cfg paths modSum mempty

-- | Load a spec by trying to parse the relevant \".spec\" file from the filesystem.
loadFromAnnotations :: ExternalPackageState -> SpecFinder m
loadFromAnnotations eps specEnv thisModule = do
  let bareSpecs = deserialiseBareSpecs thisModule eps
  case bareSpecs of
    []         -> MaybeT $ pure Nothing
    [bareSpec] -> 
      let cachedSpec = CachedSpec (ModName SrcImport (moduleName thisModule)) (WrappedSpec bareSpec)
      in pure $ SpecFound InterfaceLocation cachedSpec
    specs      -> do
      dynFlags <- lift getDynFlags
      let msg = O.text "More than one spec file found for" 
            O.<+> O.ppr thisModule O.<+> O.text ":"
            O.<+> (O.vcat $ map (O.text . show) specs)
      lift $ pluginAbort dynFlags msg
