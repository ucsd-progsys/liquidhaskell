{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
-- | This module introduces a \"lighter\" "GhcMonad" typeclass which doesn't require an instance of
-- 'ExceptionMonad', and can therefore be used for both 'CoreM' and 'Ghc'.
--

module Liquid.GHC.GhcMonadLike (
  -- * Types and type classes
    HasHscEnv
  , GhcMonadLike
  , ModuleInfo
  , TypecheckedModule(..)

  -- * Functions and typeclass methods

  , askHscEnv
  , getModuleGraph
  , getModSummary
  , lookupModSummary
  , lookupGlobalName
  , lookupName
  , modInfoLookupName
  , moduleInfoTc
  , parseModule
  , typecheckModule
  , desugarModule
  , findModule
  , lookupModule
  , isBootInterface
  , ApiComment(..)
  , apiComments
  ) where

import Control.Monad.IO.Class
import Control.Exception (throwIO)

import Data.Data (Data, gmapQr)
import Data.Generics (extQ)
import qualified Data.List
import qualified Liquid.GHC.API   as Ghc
import           Liquid.GHC.API   hiding ( ModuleInfo
                                                          , findModule
                                                          , desugarModule
                                                          , typecheckModule
                                                          , parseModule
                                                          , lookupName
                                                          , lookupGlobalName
                                                          , getModSummary
                                                          , getModuleGraph
                                                          , modInfoLookupName
                                                          , lookupModule
                                                          , TypecheckedModule
                                                          , tm_parsed_module
                                                          , tm_renamed_source
                                                          )

import GHC.Data.Maybe
import GHC.Driver.Make
import GHC.Utils.Exception (ExceptionMonad)
import qualified GHC.Core.Opt.Monad as CoreMonad
import qualified GHC.Data.EnumSet as EnumSet

import Optics

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
  askHscEnv = Hsc $ curry pure

instance (ExceptionMonad m, HasHscEnv m) => HasHscEnv (GhcT m) where
  askHscEnv = getSession

-- | A typeclass which is /very/ similar to the existing 'GhcMonad', but it doesn't impose a
-- 'ExceptionMonad' constraint.
class (Functor m, MonadIO m, HasHscEnv m, HasDynFlags m) => GhcMonadLike m

instance GhcMonadLike CoreMonad.CoreM
instance GhcMonadLike Ghc
instance GhcMonadLike (IfM lcl)
instance GhcMonadLike TcM
instance GhcMonadLike Hsc
instance (ExceptionMonad m, GhcMonadLike m) => GhcMonadLike (GhcT m)

-- NOTE(adn) Taken from the GHC API, adapted to work for a 'GhcMonadLike' monad.
getModuleGraph :: GhcMonadLike m => m ModuleGraph
getModuleGraph = fmap hsc_mod_graph askHscEnv

-- NOTE(adn) Taken from the GHC API, adapted to work for a 'GhcMonadLike' monad.
getModSummary :: GhcMonadLike m => ModuleName -> m ModSummary
getModSummary mdl = do
   mg <- fmap hsc_mod_graph askHscEnv
   let mods_by_name = [ ms | ms <- mgModSummaries mg
                      , ms_mod_name ms == mdl
                      , not (isBootInterface . isBootSummary $ ms) ]
   case mods_by_name of
     [] -> do dflags <- getDynFlags
              liftIO $ throwIO $ GhcApiError (showSDoc dflags (text "Module not part of module graph"))
     [ms] -> return ms
     multiple -> do dflags <- getDynFlags
                    liftIO $ throwIO $ GhcApiError (showSDoc dflags (text "getModSummary is ambiguous: " <+> ppr multiple))


-- Converts a 'IsBootInterface' into a 'Bool'.
isBootInterface :: IsBootInterface -> Bool
isBootInterface IsBoot  = True
isBootInterface NotBoot = False

lookupModSummary :: GhcMonadLike m => ModuleName -> m (Maybe ModSummary)
lookupModSummary mdl = do
   mg <- fmap hsc_mod_graph askHscEnv
   let mods_by_name = [ ms | ms <- mgModSummaries mg
                      , ms_mod_name ms == mdl
                      , not (isBootInterface . isBootSummary $ ms) ]
   case mods_by_name of
     [ms] -> pure (Just ms)
     _    -> pure Nothing

-- NOTE(adn) Taken from the GHC API, adapted to work for a 'GhcMonadLike' monad.
lookupGlobalName :: GhcMonadLike m => Name -> m (Maybe TyThing)
lookupGlobalName name = do
  hsc_env <- askHscEnv
  liftIO $ lookupType hsc_env name

-- NOTE(adn) Taken from the GHC API, adapted to work for a 'GhcMonadLike' monad.
lookupName :: GhcMonadLike m => Name -> m (Maybe TyThing)
lookupName name = do
  hsc_env <- askHscEnv
  liftIO $ hscTcRcLookupName hsc_env name

-- | Our own simplified version of 'ModuleInfo' to overcome the fact we cannot construct the \"original\"
-- one as the constructor is not exported, and 'getHomeModuleInfo' and 'getPackageModuleInfo' are not
-- exported either, so we had to backport them as well.
newtype ModuleInfo = ModuleInfo { minf_type_env :: UniqFM Name TyThing }

modInfoLookupName :: GhcMonadLike m
                  => ModuleInfo
                  -> Name
                  -> m (Maybe TyThing)
modInfoLookupName minf name = do
  hsc_env <- askHscEnv
  case lookupTypeEnv (minf_type_env minf) name of
    Just tyThing -> return (Just tyThing)
    Nothing      -> liftIO $ do
      lookupType hsc_env name

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
  return (ParsedModule ms (hpm_module hpm) (hpm_src_files hpm))

-- | Our own simplified version of 'TypecheckedModule'.
data TypecheckedModule = TypecheckedModule { 
    tm_parsed_module  :: ParsedModule
  , tm_renamed_source :: Maybe RenamedSource
  , tm_mod_summary    :: ModSummary
  , tm_gbl_env        :: TcGblEnv
  }

typecheckModule :: GhcMonadLike m => ParsedModule -> m TypecheckedModule
typecheckModule pmod = do
  -- Suppress all the warnings, so that they won't be printed (which would result in them being
  -- printed twice, one by GHC and once here).
  let ms = pm_mod_summary pmod
  hsc_env <- askHscEnv
  let dynFlags' = ms_hspp_opts ms
  let hsc_env_tmp = hsc_env { hsc_dflags = dynFlags' { warningFlags = EnumSet.empty } }
  (tc_gbl_env, rn_info)
        <- liftIO $ hscTypecheckRename hsc_env_tmp ms $
                       HsParsedModule { hpm_module = parsedSource pmod,
                                        hpm_src_files = pm_extra_src_files pmod }
  return TypecheckedModule {
      tm_parsed_module  = pmod
    , tm_renamed_source = rn_info
    , tm_mod_summary    = ms
    , tm_gbl_env        = tc_gbl_env
    }

{- | [NOTE:ghc810]
Something changed in the GHC bowels such that the 'hscTarget' that the 'ModSummary' was inheriting
was /not/ the one we were setting in 'configureDynFlags'. This is important, because if the 'hscTarget'
is not 'HscInterpreted' or 'HscNothing', the call to 'targetRetainsAllBindings' will yield 'False'. This
function is used internally by GHC to do dead-code-elimination and to mark functions as "exported" or not.
Therefore, the 'CoreBind's passed to LiquidHaskell would be different between GHC 8.6.5 and GHC 8.10.
-}

class IsTypecheckedModule t where
  tmParsedModule :: Lens'  t ParsedModule
  tmModSummary   :: Lens'  t ModSummary
  tmGblEnv       :: Getter t TcGblEnv

instance IsTypecheckedModule TypecheckedModule where
  tmParsedModule = lens tm_parsed_module (\s x -> s { tm_parsed_module = x })
  tmModSummary   = lens tm_mod_summary   (\s x -> s { tm_mod_summary = x })
  tmGblEnv       = to tm_gbl_env

instance IsTypecheckedModule Ghc.TypecheckedModule where
  tmParsedModule = lens Ghc.tm_parsed_module (\s x -> s { Ghc.tm_parsed_module = x })
  tmModSummary   = lens (pm_mod_summary . Ghc.tm_parsed_module)
                        (\s x -> over tmParsedModule (\pm -> pm { Ghc.pm_mod_summary = x }) s )
  tmGblEnv       = to (fst . Ghc.tm_internals_)

-- | Desugar a typechecked module.
desugarModule :: (GhcMonadLike m, IsTypecheckedModule t) => ModSummary -> t -> m ModGuts
desugarModule originalModSum typechecked = do
  -- See [NOTE:ghc810] on why we override the dynFlags here before calling 'desugarModule'.
  dynFlags          <- getDynFlags
  let modSum         = originalModSum { ms_hspp_opts = dynFlags }
  let parsedMod'     = (view tmParsedModule typechecked) { pm_mod_summary = modSum }
  let typechecked'   = set tmParsedModule parsedMod' typechecked

  hsc_env <- askHscEnv
  let hsc_env_tmp = hsc_env { hsc_dflags = ms_hspp_opts (view tmModSummary typechecked') }
  liftIO $ hscDesugar hsc_env_tmp (view tmModSummary typechecked') (view tmGblEnv typechecked')

-- | Takes a 'ModuleName' and possibly a 'UnitId', and consults the
-- filesystem and package database to find the corresponding 'Module',
-- using the algorithm that is used for an @import@ declaration.
findModule :: GhcMonadLike m => ModuleName -> Maybe FastString -> m Module
findModule mod_name maybe_pkg = do
  hsc_env <- askHscEnv
  let
    dflags   = hsc_dflags hsc_env
    this_pkg = thisPackage dflags
    throwNoModError err = throwOneError $ noModError hsc_env noSrcSpan mod_name err
  case maybe_pkg of
    Just pkg | fsToUnitId pkg /= this_pkg && pkg /= fsLit "this" -> liftIO $ do
      res <- findImportedModule hsc_env mod_name maybe_pkg
      case res of
        Found _ m -> return m
        err       -> throwNoModError err
    _otherwise -> do
      home <- lookupLoadedHomeModule mod_name
      case home of
        Just m  -> return m
        Nothing -> liftIO $ do
           res <- findImportedModule hsc_env mod_name maybe_pkg
           case res of
             Found loc m | moduleUnitId m /= this_pkg -> return m
                         | otherwise -> modNotLoadedError dflags m loc
             err -> throwNoModError err


lookupLoadedHomeModule :: GhcMonadLike m => ModuleName -> m (Maybe Module)
lookupLoadedHomeModule mod_name = do
  hsc_env <- askHscEnv
  case lookupHpt (hsc_HPT hsc_env) mod_name of
    Just mod_info      -> return (Just (mi_module (hm_iface mod_info)))
    _not_a_home_module -> return Nothing


modNotLoadedError :: DynFlags -> Module -> ModLocation -> IO a
modNotLoadedError dflags m loc = throwGhcExceptionIO $ CmdLineError $ showSDoc dflags $
   text "module is not loaded:" <+>
   quotes (ppr (moduleName m)) <+>
   parens (text (expectJust "modNotLoadedError" (ml_hs_file loc)))


lookupModule :: GhcMonadLike m => ModuleName -> Maybe FastString -> m Module
lookupModule mod_name (Just pkg) = findModule mod_name (Just pkg)
lookupModule mod_name Nothing = do
  hsc_env <- askHscEnv
  home <- lookupLoadedHomeModule mod_name
  case home of
    Just m  -> return m
    Nothing -> liftIO $ do
      res <- findExposedPackageModule hsc_env mod_name Nothing
      case res of
        Found _ m -> return m
        err       ->
          throwOneError $ noModError hsc_env noSrcSpan mod_name err

-- | Abstraction of 'EpaComment'.
data ApiComment
  = ApiLineComment String
  | ApiBlockComment String
  deriving Show

-- | Extract top-level comments from a module.
apiComments :: ParsedModule -> [Ghc.Located ApiComment]
apiComments pm =
    let hs = unLoc (pm_parsed_source pm)
        go :: forall a. Data a => a -> [LEpaComment]
        go = gmapQr (++) [] go `extQ` (id @[LEpaComment])
     in Data.List.sortOn (spanToLineColumn . getLoc) $
          mapMaybe (tokComment . toRealSrc) $ go hs
  where
    tokComment (L sp (EpaComment (EpaLineComment s) _)) = Just (L sp (ApiLineComment s))
    tokComment (L sp (EpaComment (EpaBlockComment s) _)) = Just (L sp (ApiBlockComment s))
    tokComment _ = Nothing

    -- TODO: take into account anchor_op, which only matters if the source was
    -- pre-processed by an exact-print-aware tool.
    toRealSrc (L a e) = L (RealSrcSpan (anchor a) Nothing) e

    spanToLineColumn =
      fmap (\s -> (srcSpanStartLine s, srcSpanStartCol s)) . srcSpanToRealSrcSpan
