{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}

module Liquid.GHC.GhcMonadLike (
  -- * Types and type classes
    ModuleInfo
  , TypecheckedModule(..)

  -- * Functions and typeclass methods

  , lookupModSummary
  , modInfoLookupName
  , moduleInfoTc
  , parseModule
  , typecheckModule
  , desugarModule
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
import qualified GHC.Data.EnumSet as EnumSet


lookupModSummary :: HscEnv -> ModuleName -> Maybe ModSummary
lookupModSummary hscEnv mdl = do
   let mg = hsc_mod_graph hscEnv
       mods_by_name = [ ms | ms <- mgModSummaries mg
                      , ms_mod_name ms == mdl
                      , NotBoot == isBootSummary ms ]
   case mods_by_name of
     [ms] -> Just ms
     _    -> Nothing

-- | Our own simplified version of 'ModuleInfo' to overcome the fact we cannot construct the \"original\"
-- one as the constructor is not exported, and 'getHomeModuleInfo' and 'getPackageModuleInfo' are not
-- exported either, so we had to backport them as well.
newtype ModuleInfo = ModuleInfo { minf_type_env :: UniqFM Name TyThing }

modInfoLookupName :: HscEnv
                  -> ModuleInfo
                  -> Name
                  -> IO (Maybe TyThing)
modInfoLookupName hscEnv minf name =
  case lookupTypeEnv (minf_type_env minf) name of
    Just tyThing -> return (Just tyThing)
    Nothing      -> lookupType hscEnv name

moduleInfoTc :: HscEnv -> ModSummary -> TcGblEnv -> IO ModuleInfo
moduleInfoTc hscEnv ms tcGblEnv = do
  let hsc_env_tmp = hscEnv { hsc_dflags = ms_hspp_opts ms }
  details <- md_types <$> liftIO (makeSimpleDetails hsc_env_tmp tcGblEnv)
  pure ModuleInfo { minf_type_env = details }

--
-- Parsing, typechecking and desugaring a module
--
parseModule :: HscEnv -> ModSummary -> IO ParsedModule
parseModule hscEnv ms = do
  let hsc_env_tmp = hscEnv { hsc_dflags = ms_hspp_opts ms }
  hpm <- hscParse hsc_env_tmp ms
  return (ParsedModule ms (hpm_module hpm) (hpm_src_files hpm))

-- | Our own simplified version of 'TypecheckedModule'.
data TypecheckedModule = TypecheckedModule { 
    tm_parsed_module  :: ParsedModule
  , tm_renamed_source :: Maybe RenamedSource
  , tm_mod_summary    :: ModSummary
  , tm_gbl_env        :: TcGblEnv
  }

typecheckModule :: HscEnv -> ParsedModule -> IO TypecheckedModule
typecheckModule hscEnv pmod = do
  -- Suppress all the warnings, so that they won't be printed (which would result in them being
  -- printed twice, one by GHC and once here).
  let ms = pm_mod_summary pmod
  let dynFlags' = ms_hspp_opts ms
  let hsc_env_tmp = hscEnv { hsc_dflags = dynFlags' { warningFlags = EnumSet.empty } }
  (tc_gbl_env, rn_info)
        <- hscTypecheckRename hsc_env_tmp ms $
                       HsParsedModule { hpm_module = parsedSource pmod,
                                        hpm_src_files = pm_extra_src_files pmod }
  return TypecheckedModule {
      tm_parsed_module  = pmod
    , tm_renamed_source = rn_info
    , tm_mod_summary    = ms
    , tm_gbl_env        = tc_gbl_env
    }

-- | Desugar a typechecked module.
desugarModule :: HscEnv -> ModSummary -> TypecheckedModule -> IO ModGuts
desugarModule hscEnv originalModSum typechecked = do
  -- See [NOTE:ghc810] on why we override the dynFlags here before calling 'desugarModule'.
  let modSum         = originalModSum { ms_hspp_opts = hsc_dflags hscEnv }
  let parsedMod'     = (tm_parsed_module typechecked) { pm_mod_summary = modSum }
  let typechecked'   = typechecked { tm_parsed_module = parsedMod' }

  let hsc_env_tmp = hscEnv { hsc_dflags = ms_hspp_opts (tm_mod_summary typechecked') }
  hscDesugar hsc_env_tmp (tm_mod_summary typechecked') (tm_gbl_env typechecked')

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
