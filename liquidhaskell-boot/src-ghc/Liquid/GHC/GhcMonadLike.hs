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
  , lookupModSummary
  , lookupGlobalName
  , lookupName
  , modInfoLookupName
  , moduleInfoTc
  , parseModule
  , typecheckModule
  , desugarModule
  , isBootInterface
  , ApiComment(..)
  , apiComments
  ) where

import Control.Monad.IO.Class

import Data.Data (Data, gmapQr)
import Data.Generics (extQ)
import qualified Data.List
import qualified Liquid.GHC.API   as Ghc
import           Liquid.GHC.API   hiding ( ModuleInfo
                                                          , desugarModule
                                                          , typecheckModule
                                                          , parseModule
                                                          , lookupName
                                                          , lookupGlobalName
                                                          , getModuleGraph
                                                          , modInfoLookupName
                                                          , TypecheckedModule
                                                          , tm_parsed_module
                                                          , tm_renamed_source
                                                          )

import GHC.Data.Maybe
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
