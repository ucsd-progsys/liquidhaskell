{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes   #-}

{-
Note [Module Visibility and Lookup in GHC]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
GHC distinguishes between two module visibility namespaces:

- **Regular packages** (`-package`): modules are found by `findImportedModule`,
  which searches `findExposedPackageModule`.
- **Plugin packages** (`-plugin-package`): modules are found by
  `findPluginModule`, which searches `findExposedPluginPackageModule`.

Whenever a module is looked up, we start with `findImportedModule` to check
regular packages, and if that fails, we fall back to `findPluginModule` to check
plugin packages. This allows us to support both visibility namespaces without
requiring users to mind how they specify dependencies.

-}

module Language.Haskell.Liquid.GHC.Plugin.SpecFinder
    ( findRelevantSpecs
    , LoadedSpec(..)
    , configToRedundantDependencies
    ) where

import qualified Language.Haskell.Liquid.GHC.Plugin.Serialisation as Serialisation
import           Language.Haskell.Liquid.GHC.Plugin.Types
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.UX.Config

import           Liquid.GHC.API         as GHC

import           Data.Bifunctor
import qualified Data.Char
import           Data.Maybe
import           Control.Monad (foldM, unless)
import qualified Data.HashMap.Strict as HM

-- | One selected specification in the dependency accumulator, indexed by the
-- module identity in its reference. Forcing the specification field prevents
-- a 'libTarget' selector thunk from retaining the whole decoded library and
-- its reference list.
data LoadedSpec = LoadedSpec
    !Bool
    -- ^ 'True' when selected as the target of an input module lookup, including
    -- an _LHAssumptions fallback. Such a selection takes precedence over one
    -- reached only through a saved dependency reference ('False').
    !SpecReference
    -- ^ Full module identity and payload fingerprint of the selected library.
    !LiftedSpec
    -- ^ That library's own exported specification, used for verification.

-- | Load any relevant spec for the input list of 'Module's, by querying both the 'ExternalPackageState'
-- and the 'HomePackageTable'.
--
-- Specs come from the interface files of the given modules or their matching
-- _LHAssumptions modules. A module @M@ only matches with a module named
-- @M_LHAssumptions@.
--
-- Assumptions are taken from _LHAssumptions modules only if the interface
-- file of the matching module contains no spec.
--
-- The result maps full module identities to their selected 'LoadedSpec',
-- including specifications reached through saved dependency references. Each
-- entry keeps the specification and its reference together, so the caller can
-- filter configuration-dependent exclusions once before extracting the
-- verification specifications and the references to export.
findRelevantSpecs :: Config -- ^ Assumption exclusions for this module
                  -> HscEnv
                  -> [Module]
                  -- ^ Any relevant module fetched during dependency-discovery.
                  -> TcM (HM.HashMap StableModule LoadedSpec)
findRelevantSpecs cfg hscEnv mods = foldM loadAndMerge HM.empty mods
  where
    -- Load an input module's library (or its matching assumptions), resolve its
    -- saved dependency references with mergeDependency, then select its own
    -- libTarget in the accumulator. If no library is found, leave it unchanged.
    -- "Merge" means selecting one whole LiftedSpec per module key; it does not
    -- combine fields from different specifications.
    --
    -- The first directly selected target for a key wins. A direct selection
    -- replaces a dependency-only selection, reusing its spec when references
    -- match. Process inputs in order because loading assumptions updates GHC's
    -- external package state. Force each updated map before the next input.
    loadAndMerge
      :: HM.HashMap StableModule LoadedSpec
      -> Module
      -> TcM (HM.HashMap StableModule LoadedSpec)
    loadAndMerge entries currentModule = do
      found <- loadRelevantSpec currentModule
      case found of
        Nothing -> pure entries
        Just (ref, lib) -> do
          entries' <- foldM mergeDependency entries (libDeps lib)
          let key = specModule ref
              merged = case HM.lookup key entries' of
                Just (LoadedSpec True _ _) -> entries'
                Just (LoadedSpec False oldRef spec) | oldRef == ref ->
                  HM.insert key (LoadedSpec True ref spec) entries'
                _ -> HM.insert key (LoadedSpec True ref $ libTarget lib) entries'
          -- foldM does not force its accumulator. Complete this merge before
          -- loading the next interface, including imports with no dependencies.
          merged `seq` pure merged

    -- Resolve one saved dependency reference into the accumulator. An existing
    -- direct selection is retained only if its reference matches; a mismatch
    -- is an error. A matching dependency-only selection is also reused.
    -- Otherwise load the referenced interface, check the library's fingerprint,
    -- and insert its libTarget, replacing any dependency-only selection for
    -- that module. Missing or stale specifications fail verification; loader
    -- exceptions propagate.
    --
    -- This selects a whole specification, not a field-by-field combination.
    -- The referenced library's dependencies are not traversed here: the
    -- importing library already stores its selected references as a flat list.
    mergeDependency
      :: HM.HashMap StableModule LoadedSpec
      -> SpecReference
      -> TcM (HM.HashMap StableModule LoadedSpec)
    mergeDependency entries ref = case HM.lookup (specModule ref) entries of
      Just (LoadedSpec True actual _) -> do
        checkReference ref actual
        pure entries
      Just (LoadedSpec _ oldRef _) | oldRef == ref -> pure entries
      _ -> do
        let mdl = unStableModule $ specModule ref
        -- References include package/unit identity and the exact saved spec
        -- fingerprint. Never resolve them by an unqualified module name.
        _ <- initIfaceTcRn $ loadInterface "liquidhaskell dependency" mdl ImportBySystem
        found <- liftIO $ Serialisation.deserialiseLiquidLib hscEnv mdl
        case found of
          Just (actual, lib) -> do
            checkReference ref actual
            let merged = HM.insert (specModule ref) (LoadedSpec False ref $ libTarget lib) entries
            merged `seq` pure merged
          Nothing -> failWithTc $ mkTcRnUnknownMessage $ mkPlainError [] $
            text "LiquidHaskell: missing dependency specification; rebuild dependencies:" <+> ppr mdl

    checkReference ref actual = unless (actual == ref) $
      failWithTc $ mkTcRnUnknownMessage $ mkPlainError [] $
        text "LiquidHaskell: stale dependency specification; rebuild the importing module:" <+>
        ppr (unStableModule $ specModule ref)

    loadRelevantSpec :: Module -> TcM (Maybe (SpecReference, LiquidLib))
    loadRelevantSpec currentModule = do
      res <- liftIO $ Serialisation.deserialiseLiquidLib hscEnv currentModule
      case res of
        Nothing -> loadModuleLHAssumptionsIfAny currentModule
        Just _ -> pure res

    loadModuleLHAssumptionsIfAny m | isImportExcluded m = return Nothing
                                   | otherwise = do
      let assumptionsModName = assumptionsModuleName m
      -- loadInterface might mutate the EPS if the module is
      -- not already loaded.
      --
      -- Try findImportedModule first (for -package), then fall back to
      -- findPluginModule (for -plugin-package).
      -- See Note [Module Visibility and Lookup in GHC] for details.
      res <- liftIO $ do
        r <- findImportedModule hscEnv assumptionsModName NoPkgQual
        case r of
          Found{} -> pure r
          _       -> findPluginModule hscEnv assumptionsModName
      case res of
        Found _ assumptionsMod -> do
          _ <- initIfaceTcRn $ loadInterface "liquidhaskell assumptions" assumptionsMod ImportBySystem
          liftIO $ Serialisation.deserialiseLiquidLib hscEnv assumptionsMod
        FoundMultiple{} -> failWithTc $ mkTcRnUnknownMessage $ mkPlainError [] $
                             missingInterfaceErrorDiagnostic (initIfaceMessageOpts $ hsc_dflags hscEnv) $
                             cannotFindModule hscEnv assumptionsModName res
        _ -> return Nothing

    isImportExcluded m =
      let s = takeWhile Data.Char.isAlphaNum $ unitString (moduleUnit m)
       in elem s (excludeAutomaticAssumptionsFor cfg)

    assumptionsModuleName m =
      mkModuleNameFS $ moduleNameFS (moduleName m) <> "_LHAssumptions"

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
        _ -> do
          -- Fall back to plugin package visibility
          -- See Note [Module Visibility and Lookup in GHC] for details.
          res2 <- findPluginModule env mn
          case res2 of
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
