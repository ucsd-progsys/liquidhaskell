
-- | This module introduces a \"lighter\" "GhcMonad" typeclass which doesn't require an instance of
-- 'ExceptionMonad', and can therefore be used for both 'CoreM' and 'Ghc'.
--

module Language.Haskell.Liquid.GHC.GhcMonadLike where

import Control.Monad (liftM)
import Control.Monad.IO.Class
import Control.Exception (throwIO)

import Language.Haskell.Liquid.GHC.API
import qualified CoreMonad
import DynFlags (HasDynFlags(..))
import Outputable (ppr, text, (<+>))

class HasHscEnv m where
  askHscEnv :: m HscEnv

instance HasHscEnv CoreMonad.CoreM where
  askHscEnv = CoreMonad.getHscEnv

instance HasHscEnv Ghc where
  askHscEnv = getSession

-- | A typeclass which is /very/ similar to the existing 'GhcMonad', but it doesn't impose a
-- 'ExceptionMonad' constraint.
class (Functor m, MonadIO m, HasHscEnv m, HasDynFlags m) => GhcMonadLike m

instance GhcMonadLike CoreMonad.CoreM where
instance GhcMonadLike Ghc where

getModuleGraph :: GhcMonadLike m => m ModuleGraph
getModuleGraph = liftM hsc_mod_graph askHscEnv

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

lookupGlobalName :: GhcMonadLike m => Name -> m (Maybe TyThing)
lookupGlobalName name = do
  hsc_env <- askHscEnv
  liftIO $ lookupTypeHscEnv hsc_env name

lookupName :: GhcMonadLike m => Name -> m (Maybe TyThing)
lookupName name = do
  hsc_env <- askHscEnv
  liftIO $ hscTcRcLookupName hsc_env name
