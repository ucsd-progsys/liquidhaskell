{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}

module Liquid.GHC.GhcMonadLike (
  -- * Types and type classes
    ModuleInfo

  -- * Functions and typeclass methods

  , lookupModSummary
  , modInfoLookupName
  , moduleInfoTc
  ) where

import Control.Monad.IO.Class

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
