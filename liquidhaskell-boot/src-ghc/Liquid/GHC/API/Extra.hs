{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}

module Liquid.GHC.API.Extra (
    module StableModule
  , ApiComment(..)
  , apiComments
  , apiCommentsParsedSource
  , dataConSig
  , desugarModuleIO
  , fsToUnitId
  , isPatErrorAlt
  , lookupModSummary
  , modInfoLookupNameIO
  , moduleInfoTc
  , parseModuleIO
  , qualifiedNameFS
  , relevantModules
  , renderWithStyle
  , showPprQualified
  , showSDocQualified
  , splitDollarApp
  , strictNothing
  , thisPackage
  , tyConRealArity
  , typecheckModuleIO
  , untick
  ) where

import Control.Monad.IO.Class
import           Liquid.GHC.API.StableModule      as StableModule
import GHC
import Data.Data (Data, gmapQr)
import Data.Generics (extQ)
import Data.Foldable                  (asum)
import Data.List                      (foldl', sortOn)
import qualified Data.Map as Map
import qualified Data.Set as S
import GHC.Builtin.Names ( dollarIdKey )
import GHC.Core                       as Ghc
import GHC.Core.Coercion              as Ghc
import GHC.Core.DataCon               as Ghc
import GHC.Core.Make                  (pAT_ERROR_ID)
import GHC.Core.Type                  as Ghc hiding (typeKind , isPredTy, extendCvSubst, linear)
import GHC.Data.FastString            as Ghc
import qualified GHC.Data.EnumSet as EnumSet
import GHC.Data.Maybe
import qualified GHC.Data.Strict
import GHC.Driver.Env
import GHC.Driver.Main
import GHC.Driver.Session             as Ghc
import GHC.Tc.Types
import GHC.Types.Name                 (isSystemName, nameModule_maybe, occNameFS)
import GHC.Types.SrcLoc               as Ghc
import GHC.Types.TypeEnv
import GHC.Types.Unique               (getUnique, hasKey)
import GHC.Types.Unique.FM

import GHC.Unit.Module.Deps           as Ghc (Dependencies(dep_direct_mods))
import GHC.Unit.Module.Graph          as Ghc
  ( NodeKey(NodeKey_Module)
  , ModNodeKeyWithUid(ModNodeKeyWithUid)
  , mgTransDeps
  )
import GHC.Unit.Module.ModDetails     (md_types)
import GHC.Unit.Module.ModSummary     (isBootSummary)
import GHC.Utils.Outputable           as Ghc hiding ((<>))

import GHC.Unit.Module
import GHC.Unit.Module.ModGuts
import GHC.Unit.Module.Deps (Usage(..))

-- 'fsToUnitId' is gone in GHC 9, but we can bring code it in terms of 'fsToUnit' and 'toUnitId'.
fsToUnitId :: FastString -> UnitId
fsToUnitId = toUnitId . fsToUnit

thisPackage :: DynFlags -> UnitId
thisPackage = homeUnitId_

-- See NOTE [tyConRealArity].
tyConRealArity :: TyCon -> Int
tyConRealArity tc = go 0 (tyConKind tc)
  where
    go :: Int -> Kind -> Int
    go !acc k =
      case asum [fmap (\(_, _, _, c) -> c) (splitFunTy_maybe k), fmap snd (splitForAllTyCoVar_maybe k)] of
        Nothing -> acc
        Just ks -> go (acc + 1) ks

getDependenciesModuleNames :: ModuleGraph -> UnitId -> Dependencies -> [ModuleNameWithIsBoot]
getDependenciesModuleNames mg unitId deps =
    mapMaybe nodeKeyToModuleName $ S.toList $ S.unions $ catMaybes
      [ Map.lookup k tdeps
      | (_, m) <- S.toList $ dep_direct_mods deps
      , let k = NodeKey_Module $ ModNodeKeyWithUid m unitId
      ]
  where
    tdeps = mgTransDeps mg
    nodeKeyToModuleName (NodeKey_Module (ModNodeKeyWithUid m _)) = Just m
    nodeKeyToModuleName _ = Nothing

renderWithStyle :: DynFlags -> SDoc -> PprStyle -> String
renderWithStyle dynflags sdoc style = Ghc.renderWithContext (Ghc.initSDocContext dynflags style) sdoc

-- This function is gone in GHC 9.
dataConSig :: DataCon -> ([TyCoVar], ThetaType, [Type], Type)
dataConSig dc
  = (dataConUnivAndExTyCoVars dc, dataConTheta dc, map irrelevantMult $ dataConOrigArgTys dc, dataConOrigResTy dc)

-- | The collection of dependencies and usages modules which are relevant for liquidHaskell
relevantModules :: ModuleGraph -> ModGuts -> S.Set Module
relevantModules mg modGuts = used `S.union` dependencies
  where
    dependencies :: S.Set Module
    dependencies = S.fromList $ map (toModule . gwib_mod)
                              . filter ((NotBoot ==) . gwib_isBoot)
                              . getDependenciesModuleNames mg thisUnitId $ deps

    deps :: Dependencies
    deps = mg_deps modGuts

    thisModule :: Module
    thisModule = mg_module modGuts

    thisUnitId = moduleUnitId thisModule

    toModule :: ModuleName -> Module
    toModule = unStableModule . mkStableModule thisUnitId

    used :: S.Set Module
    used = S.fromList $ foldl' collectUsage mempty . mg_usages $ modGuts
      where
        collectUsage :: [Module] -> Usage -> [Module]
        collectUsage acc = \case
          UsagePackageModule     { usg_mod      = modl    } -> modl : acc
          UsageHomeModule        { usg_mod_name = modName } -> toModule modName : acc
          UsageMergedRequirement { usg_mod      = modl    } -> modl : acc
          _ -> acc

--
-- Parsing, typechecking and desugaring a module
--
parseModuleIO :: HscEnv -> ModSummary -> IO ParsedModule
parseModuleIO hscEnv ms = do
  let hsc_env_tmp = hscEnv { hsc_dflags = ms_hspp_opts ms }
  hpm <- hscParse hsc_env_tmp ms
  return (ParsedModule ms (hpm_module hpm) (hpm_src_files hpm))

-- | Our own simplified version of 'TypecheckedModule'.
data TypecheckedModuleLH = TypecheckedModuleLH {
    tmlh_parsed_module  :: ParsedModule
  , tmlh_renamed_source :: Maybe RenamedSource
  , tmlh_mod_summary    :: ModSummary
  , tmlh_gbl_env        :: TcGblEnv
  }

typecheckModuleIO :: HscEnv -> ParsedModule -> IO TypecheckedModuleLH
typecheckModuleIO hscEnv pmod = do
  -- Suppress all the warnings, so that they won't be printed (which would result in them being
  -- printed twice, one by GHC and once here).
  let ms = pm_mod_summary pmod
  let dynFlags' = ms_hspp_opts ms
  let hsc_env_tmp = hscEnv { hsc_dflags = dynFlags' { warningFlags = EnumSet.empty } }
  (tc_gbl_env, rn_info)
        <- hscTypecheckRename hsc_env_tmp ms $
                       HsParsedModule { hpm_module = parsedSource pmod,
                                        hpm_src_files = pm_extra_src_files pmod }
  return TypecheckedModuleLH {
      tmlh_parsed_module  = pmod
    , tmlh_renamed_source = rn_info
    , tmlh_mod_summary    = ms
    , tmlh_gbl_env        = tc_gbl_env
    }

-- | Desugar a typechecked module.
desugarModuleIO :: HscEnv -> ModSummary -> TypecheckedModuleLH -> IO ModGuts
desugarModuleIO hscEnv originalModSum typechecked = do
  -- See [NOTE:ghc810] on why we override the dynFlags here before calling 'desugarModule'.
  let modSum         = originalModSum { ms_hspp_opts = hsc_dflags hscEnv }
  let parsedMod'     = (tmlh_parsed_module typechecked) { pm_mod_summary = modSum }
  let typechecked'   = typechecked { tmlh_parsed_module = parsedMod' }

  let hsc_env_tmp = hscEnv { hsc_dflags = ms_hspp_opts (tmlh_mod_summary typechecked') }
  hscDesugar hsc_env_tmp (tmlh_mod_summary typechecked') (tmlh_gbl_env typechecked')

-- | Abstraction of 'EpaComment'.
data ApiComment
  = ApiLineComment String
  | ApiBlockComment String
  deriving (Eq, Show)

-- | Extract top-level comments from a module.
apiComments :: ParsedModule -> [Ghc.Located ApiComment]
apiComments pm = apiCommentsParsedSource (pm_parsed_source pm)

apiCommentsParsedSource :: Located (HsModule GhcPs) -> [Ghc.Located ApiComment]
apiCommentsParsedSource ps =
    let hs = unLoc ps
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
    toRealSrc (L a e) = L (RealSrcSpan (anchor a) strictNothing) e

    spanToLineColumn =
      fmap (\s -> (srcSpanStartLine s, srcSpanStartCol s)) . srcSpanToRealSrcSpan

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
newtype ModuleInfoLH = ModuleInfoLH { minflh_type_env :: UniqFM Name TyThing }

modInfoLookupNameIO :: HscEnv
                  -> ModuleInfoLH
                  -> Name
                  -> IO (Maybe TyThing)
modInfoLookupNameIO hscEnv minf name =
  case lookupTypeEnv (minflh_type_env minf) name of
    Just tyThing -> return (Just tyThing)
    Nothing      -> lookupType hscEnv name

moduleInfoTc :: HscEnv -> TcGblEnv -> IO ModuleInfoLH
moduleInfoTc hscEnv tcGblEnv = do
  details <- md_types <$> liftIO (makeSimpleDetails (hsc_logger hscEnv) tcGblEnv)
  pure ModuleInfoLH { minflh_type_env = details }

-- | Tells if a case alternative calls to patError
isPatErrorAlt :: CoreAlt -> Bool
isPatErrorAlt (Alt _ _ exprCoreBndr) = hasPatErrorCall exprCoreBndr
  where
   hasPatErrorCall :: CoreExpr -> Bool
   -- auto generated undefined case: (\_ -> (patError @levity @type "error message")) void
   -- Type arguments are erased before calling isUndefined
   hasPatErrorCall (App (Var x) _) = x == pAT_ERROR_ID
   -- another auto generated undefined case:
   -- let lqanf_... = patError "error message") in case lqanf_... of {}
   hasPatErrorCall (Let (NonRec x e) (Case (Var v) _ _ []))
     | x == v = hasPatErrorCall e
   hasPatErrorCall (Let _ e) = hasPatErrorCall e
   -- otherwise
   hasPatErrorCall _ = False


qualifiedNameFS :: Name -> FastString
qualifiedNameFS n = concatFS [modFS, occFS, uniqFS]
  where
  modFS = case nameModule_maybe n of
            Nothing -> fsLit ""
            Just m  -> concatFS [moduleNameFS (moduleName m), fsLit "."]

  occFS = occNameFS (getOccName n)
  uniqFS
    | isSystemName n
    = concatFS [fsLit "_",  fsLit (showPprQualified (getUnique n))]
    | otherwise
    = fsLit ""

-- Variants of Outputable functions which now require DynFlags!
showPprQualified :: Outputable a => a -> String
showPprQualified = showSDocQualified . ppr

showSDocQualified :: Ghc.SDoc -> String
showSDocQualified = Ghc.renderWithContext ctx
  where
    style = Ghc.mkUserStyle myQualify Ghc.AllTheWay
    ctx = Ghc.defaultSDocContext { sdocStyle = style }

myQualify :: Ghc.NamePprCtx
myQualify = Ghc.neverQualify { Ghc.queryQualifyName = Ghc.alwaysQualifyNames }
-- { Ghc.queryQualifyName = \_ _ -> Ghc.NameNotInScope1 }


strictNothing :: GHC.Data.Strict.Maybe a
strictNothing = GHC.Data.Strict.Nothing

splitDollarApp :: CoreExpr -> Maybe (CoreExpr, CoreExpr)
splitDollarApp e
     -- matches `$ t1 t2 t3 t4 f a`
     | App e1 a  <- untick e
     , App e2 f  <- untick e1
     , App e3 t4 <- untick e2
     , App e4 t3 <- untick e3
     , App e5 t2 <- untick e4
     , App d t1  <- untick e5
     , Var v     <- untick d
     , v `hasKey` dollarIdKey
     , Type _    <- untick t1
     , Type _    <- untick t2
     , Type _    <- untick t3
     , Type _    <- untick t4
     = Just (f, a)
     | otherwise
     = Nothing

untick :: CoreExpr -> CoreExpr
untick (Tick _ e) = untick e
untick e = e
