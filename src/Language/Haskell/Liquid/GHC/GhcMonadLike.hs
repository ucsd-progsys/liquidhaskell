{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
-- | This module introduces a \"lighter\" "GhcMonad" typeclass which doesn't require an instance of
-- 'ExceptionMonad', and can therefore be used for both 'CoreM' and 'Ghc'.
--

module Language.Haskell.Liquid.GHC.GhcMonadLike where

import Control.Monad
import Control.Monad.IO.Class
import Control.Exception (throwIO)

import Data.IORef (readIORef)
import Data.Maybe

import Language.Haskell.Liquid.GHC.API hiding (ModuleInfo)
import qualified CoreMonad
import DynFlags (HasDynFlags(..))
import TcRnMonad
import Outputable (showSDocUnsafe, ppr, text, (<+>), vcat)
import UniqFM
import Avail

class HasHscEnv m where
  askHscEnv :: m HscEnv

instance HasHscEnv CoreMonad.CoreM where
  askHscEnv = CoreMonad.getHscEnv

instance HasHscEnv Ghc where
  askHscEnv = getSession

instance HasHscEnv (IfM lcl) where
  askHscEnv = getTopEnv

instance HasHscEnv TcM where
  askHscEnv = env_top <$> getEnv

instance HasHscEnv Hsc where
  askHscEnv = Hsc $ \e w -> pure (e, w)

-- | A typeclass which is /very/ similar to the existing 'GhcMonad', but it doesn't impose a
-- 'ExceptionMonad' constraint.
class (Functor m, MonadIO m, HasHscEnv m, HasDynFlags m) => GhcMonadLike m

instance GhcMonadLike CoreMonad.CoreM
instance GhcMonadLike Ghc
instance GhcMonadLike (IfM lcl)
instance GhcMonadLike TcM
instance GhcMonadLike Hsc

-- NOTE(adn) Taken from the GHC API, adapted to work for a 'GhcMonadLike' monad.
getModuleGraph :: GhcMonadLike m => m ModuleGraph
getModuleGraph = liftM hsc_mod_graph askHscEnv

-- NOTE(adn) Taken from the GHC API, adapted to work for a 'GhcMonadLike' monad.
getModSummary :: GhcMonadLike m => ModuleName -> m ModSummary
getModSummary mod = do
   mg <- liftM hsc_mod_graph askHscEnv
   let mods_by_name = [ ms | ms <- mgModSummaries mg
                      , ms_mod_name ms == mod
                      , not (isBootSummary ms) ]
   case mods_by_name of
     [] -> do dflags <- getDynFlags
              liftIO $ throwIO $ mkApiErr dflags (text "Module not part of module graph")
     [ms] -> return ms
     multiple -> do dflags <- getDynFlags
                    liftIO $ throwIO $ mkApiErr dflags (text "getModSummary is ambiguous: " <+> ppr multiple)

-- NOTE(adn) Taken from the GHC API, adapted to work for a 'GhcMonadLike' monad.
lookupGlobalName :: GhcMonadLike m => Name -> m (Maybe TyThing)
lookupGlobalName name = do
  hsc_env <- askHscEnv
  liftIO $ lookupTypeHscEnv hsc_env name

-- NOTE(adn) Taken from the GHC API, adapted to work for a 'GhcMonadLike' monad.
lookupName :: GhcMonadLike m => Name -> m (Maybe TyThing)
lookupName name = do
  hsc_env <- askHscEnv
  liftIO $ hscTcRcLookupName hsc_env name

-- | Our own simplified version of 'ModuleInfo' to overcome the fact we cannot construct the \"original\"
-- one as the constructor is not exported, and 'getHomeModuleInfo' and 'getPackageModuleInfo' are not
-- exported either, so we had to backport them as well.
data ModuleInfo = ModuleInfo { minf_type_env :: UniqFM TyThing }

modInfoLookupName :: GhcMonadLike m 
                  => ModuleInfo 
                  -> Name
                  -> m (Maybe TyThing)
modInfoLookupName minf name = do
  hsc_env <- askHscEnv
  case lookupTypeEnv (minf_type_env minf) name of
    Just tyThing -> return (Just tyThing)
    Nothing      -> do
      eps   <- liftIO $ readIORef (hsc_EPS hsc_env)
      return $! lookupType (hsc_dflags hsc_env) (hsc_HPT hsc_env) (eps_PTE eps) name

moduleInfoTc :: GhcMonadLike m => ModSummary -> TcGblEnv -> m ModuleInfo
moduleInfoTc ms tcGblEnv = do
  hsc_env <- askHscEnv
  let hsc_env_tmp = hsc_env { hsc_dflags = ms_hspp_opts ms }
  details <- md_types <$> liftIO (makeSimpleDetails hsc_env_tmp tcGblEnv)
  pure ModuleInfo { minf_type_env = details }

--
-- Parsing, typechecking and desugaring a module
--
parseModule :: GhcMonadLike m => ModSummary -> m ParsedModule
parseModule ms = do
  hsc_env <- askHscEnv
  let hsc_env_tmp = hsc_env { hsc_dflags = ms_hspp_opts ms }
  hpm <- liftIO $ hscParse hsc_env_tmp ms
  return (ParsedModule ms (hpm_module hpm) (hpm_src_files hpm)
                           (hpm_annotations hpm))


typecheckModule :: GhcMonadLike m => ParsedModule -> m (ModSummary, TcGblEnv)
typecheckModule pmod = do
  let ms = pm_mod_summary pmod
  hsc_env <- askHscEnv
  let hsc_env_tmp = hsc_env { hsc_dflags = ms_hspp_opts ms }
  (tc_gbl_env, _)
        <- liftIO $ hscTypecheckRename hsc_env_tmp ms $
                       HsParsedModule { hpm_module = parsedSource pmod,
                                        hpm_src_files = pm_extra_src_files pmod,
                                        hpm_annotations = pm_annotations pmod }
  return (ms, tc_gbl_env)


-- | Desugar a typechecked module.
desugarModule :: GhcMonadLike m => (ModSummary, TcGblEnv) -> m ModGuts
desugarModule (ms, tcg) = do
  hsc_env <- askHscEnv
  let hsc_env_tmp = hsc_env { hsc_dflags = ms_hspp_opts ms }
  liftIO $ hscDesugar hsc_env_tmp ms tcg
