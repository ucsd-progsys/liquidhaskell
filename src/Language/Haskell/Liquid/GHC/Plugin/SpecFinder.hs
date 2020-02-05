{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes   #-}

module Language.Haskell.Liquid.GHC.Plugin.SpecFinder
    ( findRelevantSpecs
    , SpecFinderResult(..)
    , SearchLocation(..)
    ) where

import           Language.Haskell.Liquid.Measure          ( BareSpec )
import           Language.Haskell.Liquid.GHC.GhcMonadLike as GhcMonadLike ( GhcMonadLike, askHscEnv, getModSummary )
import           Language.Haskell.Liquid.GHC.Plugin.Util  ( pluginAbort, deserialiseBareSpecs )
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.GHC.Interface

import qualified Outputable                              as O
import           Module                                   ( Module, lookupModuleEnv, extendModuleEnv )
import           GHC
import           HscTypes
import           CoreMonad                                ( getDynFlags )

import qualified Data.HashSet                            as HS
import           Data.Foldable

import           Control.Applicative                      ( (<|>) )
import           Control.Monad.Trans                      ( lift )
import           Control.Monad.Trans.Maybe

type SpecFinder m = GhcMonadLike m => SpecEnv -> Module -> MaybeT m SpecFinderResult

-- | The result of searching for a spec.
data SpecFinderResult = 
    SpecNotFound ModuleName
  | SpecFound SearchLocation Module (ModName, BareSpec)

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
                  -> [Module]
                  -> m [SpecFinderResult]
findRelevantSpecs cfg eps specEnv = foldlM loadRelevantSpec mempty
  where
    loadRelevantSpec :: [SpecFinderResult] -> Module -> m [SpecFinderResult]
    loadRelevantSpec !acc mod = do
      let finders = asum [ lookupCachedSpec specEnv mod 
                         , loadFromAnnotations eps specEnv mod
                         , loadSpecFromDisk cfg specEnv mod
                         ]
      res <- runMaybeT finders
      case res of
        Nothing         -> pure $ SpecNotFound (moduleName mod) : acc
        Just specResult -> pure (specResult : acc)

-- | Try to load the spec from the 'SpecEnv'.
lookupCachedSpec :: SpecFinder m
lookupCachedSpec specEnv mod = do
  r <- MaybeT $ pure (lookupModuleEnv specEnv mod)
  pure $ SpecFound SpecEnvLocation mod r

-- | Load a spec by trying to parse the relevant \".spec\" file from the filesystem.
loadSpecFromDisk :: Config -> SpecFinder m
loadSpecFromDisk cfg specEnv thisModule = do
  modSummary <- lift $ GhcMonadLike.getModSummary (moduleName thisModule)
  bareSpecs  <- lift $ findExternalSpecs cfg modSummary
  case bareSpecs of
    []         -> MaybeT $ pure Nothing
    [bareSpec] -> pure $ SpecFound DiskLocation thisModule bareSpec
    specs      -> do
      dynFlags <- lift getDynFlags
      let msg = O.text "More than one spec file found for" 
            O.<+> O.ppr thisModule O.<+> O.text ":"
            O.<+> (O.vcat $ map (O.text . show) specs)
      lift $ pluginAbort dynFlags msg

findExternalSpecs :: GhcMonadLike m 
                  => Config 
                  -> ModSummary 
                  -> m [(ModName, BareSpec)]
findExternalSpecs cfg modSum =
  let paths = HS.fromList $ idirs cfg ++ importPaths (ms_hspp_opts modSum)
  in findAndParseSpecFiles cfg paths modSum mempty -- reachable: mempty

-- | Load a spec by trying to parse the relevant \".spec\" file from the filesystem.
loadFromAnnotations :: ExternalPackageState -> SpecFinder m
loadFromAnnotations eps specEnv thisModule = do
  let bareSpecs = deserialiseBareSpecs thisModule eps
  case bareSpecs of
    []         -> MaybeT $ pure Nothing
    [bareSpec] -> pure $ SpecFound InterfaceLocation thisModule (ModName SrcImport (moduleName thisModule), bareSpec)
    specs      -> do
      dynFlags <- lift getDynFlags
      let msg = O.text "More than one spec file found for" 
            O.<+> O.ppr thisModule O.<+> O.text ":"
            O.<+> (O.vcat $ map (O.text . show) specs)
      lift $ pluginAbort dynFlags msg
