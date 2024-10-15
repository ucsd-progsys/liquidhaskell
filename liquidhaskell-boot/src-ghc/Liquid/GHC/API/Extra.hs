{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}

module Liquid.GHC.API.Extra (
    module StableModule
  , ApiComment(..)
  , addNoInlinePragmasToLocalBinds
  , apiComments
  , apiCommentsParsedSource
  , dataConSig
  , fsToUnitId
  , isPatErrorAlt
  , lookupModSummary
  , minus_RDR
  , modInfoLookupName
  , moduleInfoTc
  , qualifiedNameFS
  , relevantModules
  , renderWithStyle
  , showPprQualified
  , showPprDebug
  , showSDocQualified
  , splitDollarApp
  , strictNothing
  , thisPackage
  , tyConRealArity
  , untick
  ) where

import Control.Monad.IO.Class
import           Liquid.GHC.API.StableModule      as StableModule
import GHC hiding (modInfoLookupName)
import Data.Data (Data, gmapQr, gmapT)
import Data.Generics (extQ, extT)
import Data.Foldable                  (asum)
import Data.List                      (sortOn)
import qualified Data.Map as Map
import qualified Data.Set as S
import GHC.Builtin.Names ( dollarIdKey, minusName )
import GHC.Core                       as Ghc
import GHC.Core.Coercion              as Ghc
import GHC.Core.DataCon               as Ghc
import GHC.Core.Make                  (pAT_ERROR_ID)
import GHC.Core.Type                  as Ghc hiding (typeKind , isPredTy, extendCvSubst, linear)
import GHC.Data.Bag                   (bagToList)
import GHC.Data.FastString            as Ghc
import GHC.Data.Maybe
import qualified GHC.Data.Strict
import GHC.Driver.Env
import GHC.Driver.Main
import GHC.Driver.Session             as Ghc
import GHC.Tc.Types
import GHC.Types.Basic
import GHC.Types.Name                 (isSystemName, nameModule_maybe, occNameFS)
import GHC.Types.Name.Reader          (nameRdrName, rdrNameOcc)
import GHC.Types.SourceText           (SourceText(..))
import GHC.Types.SrcLoc               as Ghc
import GHC.Types.TypeEnv
import GHC.Types.Unique               (getUnique, hasKey)

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

-- | Adds NOINLINE pragmas to all local bindings in the module.
--
-- This prevents the simple optimizer from inlining such bindings which might
-- have specs that would otherwise be left dangling.
--
-- https://gitlab.haskell.org/ghc/ghc/-/issues/24386
--
addNoInlinePragmasToLocalBinds :: ParsedModule -> ParsedModule
addNoInlinePragmasToLocalBinds ps =
    ps { pm_parsed_source = go (pm_parsed_source ps) }
  where
    go :: forall a. Data a => a -> a
    go = gmapT ((id `extT` addNoInlinePragmas) . go)

    addNoInlinePragmas :: HsValBinds GhcPs -> HsValBinds GhcPs
    addNoInlinePragmas = \case
      ValBinds x binds sigs ->
          ValBinds x binds (newSigs ++ dropInlinePragmas sigs)
        where
          dropInlinePragmas = filter (not . isInlineSig . unLoc)

          isInlineSig InlineSig{} = True
          isInlineSig _ = False

          newSigs = concatMap (traverse noInlinePragmaForBind) $ bagToList binds

          noInlinePragmaForBind :: HsBindLR GhcPs GhcPs -> [Sig GhcPs]
          noInlinePragmaForBind bndr =
              [ InlineSig
                  []
                  (noLocA b)
                  defaultInlinePragma
                    { inl_inline = NoInline $ SourceText $ occNameFS $ rdrNameOcc b
                    , inl_act = NeverActive
                    }
              | b <- collectHsBindBinders CollNoDictBinders bndr
              ]

      bnds -> bnds


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
newtype ModuleInfoLH = ModuleInfoLH { minflh_type_env :: TypeEnv }

modInfoLookupName :: (GhcMonad m) => ModuleInfoLH -> Name -> m (Maybe TyThing)
modInfoLookupName minf name = do
  case lookupTypeEnv (minflh_type_env minf) name of
    Just tyThing -> return (Just tyThing)
    Nothing      -> lookupGlobalName name

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
   hasPatErrorCall (App e _)
     | Var x <- unTick e = x == pAT_ERROR_ID
     | otherwise = hasPatErrorCall e
   -- another auto generated undefined case:
   -- let lqanf_... = patError "error message") in case lqanf_... of {}
   hasPatErrorCall (Let (NonRec x e) ec)
     | Case e0 _ _ [] <- unTick ec
     , Var v <- unTick e0
     , x == v = hasPatErrorCall e
   hasPatErrorCall (Case e _ _ _) = hasPatErrorCall e
   hasPatErrorCall (Let _ e) = hasPatErrorCall e
   hasPatErrorCall (Tick _ e) = hasPatErrorCall e
   -- otherwise
   hasPatErrorCall _ = False

   unTick (Tick _ e) = unTick e
   unTick e = e


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

showPprDebug :: Outputable a => a -> String
showPprDebug = showSDocDebug . ppr

showSDocDebug :: Ghc.SDoc -> String
showSDocDebug = Ghc.renderWithContext ctx
  where
    style = Ghc.mkUserStyle myQualify Ghc.AllTheWay
    ctx = Ghc.defaultSDocContext {
        sdocStyle = style
      , sdocPprDebug = True
      }

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

minus_RDR :: RdrName
minus_RDR = nameRdrName minusName
