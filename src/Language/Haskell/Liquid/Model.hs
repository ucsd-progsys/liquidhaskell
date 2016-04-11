{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
module Language.Haskell.Liquid.Model where

import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Bifunctor
import qualified Data.HashMap.Strict                   as HM
import           Data.Maybe
import           Data.Proxy
import           Data.Typeable
import           GHC.Prim
import           Text.PrettyPrint.HughesPJ
import           Unsafe.Coerce

import           Language.Fixpoint.Types (FixResult(..), Symbol, symbol, Sort(..), Expr(..), mkSubst,
                                          subst)
import           Language.Fixpoint.Smt.Interface
import           Language.Haskell.Liquid.GHC.Interface
import           Language.Haskell.Liquid.Types         hiding (var)
import           Language.Haskell.Liquid.Types.RefType
import           Test.Target.Expr
import           Test.Target.Monad
import           Test.Target.Targetable
import           Test.Target.Testable
import           Test.Target.Util

import           Bag
import           GHC hiding (obtainTermFromVal)
import           GHC.Paths
import qualified Outputable as GHC
import           DynFlags
import           HscMain
import           InstEnv
import           OccName
import           RdrName
import           Type
import           TysWiredIn
import           InteractiveEval

import Id
import ByteCodeGen      ( byteCodeGen, coreExprToBCOs )
import Linker
import CoreTidy         ( tidyExpr )
import Type             ( Type )
import {- Kind parts of -} Type         ( Kind )
import CoreLint         ( lintInteractiveExpr )
import VarEnv           ( emptyTidyEnv )
import Panic
import ConLike
import Control.Concurrent
import Module
import Packages
import RdrName
import HsSyn
import CoreSyn
import StringBuffer
import Parser
import Lexer
import SrcLoc
import TcRnDriver
import TcIface          ( typecheckIface )
import TcRnMonad
import IfaceEnv         ( initNameCache )
import LoadIface        ( ifaceStats, initExternalPackageState )
import PrelInfo
import MkIface
import Desugar
import SimplCore
import TidyPgm
import CorePrep
import CoreToStg        ( coreToStg )
import qualified StgCmm ( codeGen )
import StgSyn
import CostCentre
import ProfInit
import TyCon
import Name
import SimplStg         ( stg2stg )
import Cmm
import CmmParse         ( parseCmmFile )
import CmmBuildInfoTables
import CmmPipeline
import CmmInfo
import CodeOutput
import NameEnv          ( emptyNameEnv )
import InstEnv
import FamInstEnv
import Fingerprint      ( Fingerprint )
import Hooks
import Maybes

import DynFlags
import ErrUtils

import UniqFM
import NameEnv
import HscStats         ( ppSourceStats )
import HscTypes
import FastString
import UniqSupply
import Bag
import Exception
import qualified Stream
import Stream (Stream)

import Util

import Data.List
import Control.Monad
import Data.IORef
import System.FilePath as FilePath
import System.Directory
import qualified Data.Map as Map


import           Debug.Trace

getModels :: GhcInfo -> Config -> FixResult Cinfo -> IO (FixResult Cinfo)
getModels info cfg fi = case fi of
  Unsafe cs -> fmap Unsafe . GHC.runGhc (Just libdir) $ do
    setSession (env info)
    imps <- getContext
    setContext (IIModule (mkModuleName "ListElem") -- FIXME
               : IIDecl ((simpleImportDecl (mkModuleName "Test.Target.Targetable"))
                                           { ideclQualified = True })
               : imps)
    --             -- needed for defaulted tyvars
    --             -- : IIDecl ((simpleImportDecl (mkModuleName "GHC.Integer.Type"))
    --             --                           { ideclQualified = True })
    --             : imps)
    mapM (getModel info cfg) cs
  _         -> return fi
  where
  mbenv = Nothing -- Just (env info)


getModel :: GhcInfo -> Config -> Cinfo -> Ghc Cinfo
getModel info cfg ci@(Ci { ci_err = Just err@(ErrSubType { ctx, tact, texp }) }) = do
  let vts = HM.toList ctx
  liftIO $ print $ map fst vts
  vtds <- addDicts vts
  liftIO $ print $ map (\(x,_,_) -> x) vtds

  hsc_env <- getSession
  df <- getDynFlags
  let opts = defaultOpts
  smt <- liftIO $ makeContext False (solver opts) (target info)
  model <- liftIO $ runTarget opts (initState (target info) (spec info) smt df) $ do
    cs <- gets constructors
    traceShowM ("constructors", cs)
    su <- mkSubst . map (second EVar) <$> gets freesyms
    traceShowM ("su", su)
    n <- asks depth
    vs <- forM vtds $ \(v, t, TargetDict d@Dict) -> do
      traceShowM ("QUERY", v, t)
      modify $ \s@(TargetState {..}) -> s { variables = (v,getType (dictProxy d)) : variables }
      query (dictProxy d) n v (subst su t)
    traceM "DONE QUERY"
    setup
    traceM "DONE SETUP"
    _ <- liftIO $ command smt CheckSat
    traceM "DONE CHECKSAT"
    forM (zip vs vtds) $ \(sv, (v, t, TargetDict d@Dict)) -> do
      x <- decode sv t
      n <- asks depth
      xt <- liftIO $ obtainTermFromVal hsc_env 100 True (toType t) (x `asTypeOfDict` d)
      return (v, text (GHC.showPpr df xt)) -- (toExpr (x `asTypeOfDict` d))))
  traceM "DONE DECODE"
  traceShowM model
  -- let model = mempty

  _ <- liftIO $ cleanupContext smt
  return (ci { ci_err = Just (err { model = HM.fromList model })})

getModel _ _ ci = return ci

dictProxy :: forall t. Dict (Targetable t) -> Proxy t
dictProxy Dict = Proxy

asTypeOfDict :: forall t. t -> Dict (Targetable t) -> t
x `asTypeOfDict` Dict = x

data Dict :: Constraint -> * where
  Dict :: a => Dict a
  deriving Typeable

data TargetDict = forall t. TargetDict (Dict (Targetable t))

addDicts :: [(Symbol, SpecType)] -> Ghc [(Symbol, SpecType, TargetDict)]
addDicts bnds = catMaybes <$> mapM addDict bnds

addDict :: (Symbol, SpecType) -> Ghc (Maybe (Symbol, SpecType, TargetDict))
addDict (v, t) = do
  let mt = monomorphize (toType t)
  case tyConAppTyCon_maybe mt of
    Nothing -> return Nothing
    Just tc | isClassTyCon tc  -> return Nothing
    Just tc -> do
      getInfo False (getName tc) >>= \case
        Nothing -> return Nothing
        Just (ATyCon tc, _, cis, _) -> do
          df <- getDynFlags

          genericsMod   <- lookupModule (mkModuleName "GHC.Generics") Nothing
          targetableMod <- lookupModule (mkModuleName "Test.Target.Targetable") Nothing
          modelMod      <- lookupModule (mkModuleName "Language.Haskell.Liquid.Model") Nothing

          let genericClsName    = mkOrig genericsMod (mkClsOcc "Generic")
          let targetableClsName = mkOrig targetableMod (mkClsOcc "Targetable")
          let dictTcName        = mkOrig modelMod (mkTcOcc "Dict")
          let dictDataName      = mkOrig modelMod (mkDataOcc "Dict")

          -- let mt = monomorphize (toType t)

          -- maybe add a Targetable instance
          unless ("Test.Target.Targetable.Targetable"
                  `elem` map (showpp.is_cls_nm) cis) $ do

            -- maybe derive a Generic instance
            unless ("GHC.Generics.Generic"
                    `elem` map (showpp.is_cls_nm) cis) $ do
              let tvs = map (getRdrName) (tyConTyVars tc)
              let tvbnds = userHsTyVarBndrs noSrcSpan tvs
              let genericInst = nlHsTyConApp genericClsName
                               [nlHsTyConApp (getRdrName tc) (map nlHsTyVar tvs)]
              let instType = noLoc $ HsForAllTy Implicit Nothing
                             (HsQTvs [] tvbnds)
                             (noLoc []) -- (noLoc (map (nlHsTyConApp genericClsName . pure . nlHsTyVar) tvs))
                             genericInst
              let derivDecl = DerivD $ DerivDecl instType Nothing
              traceShowM (GHC.showPpr df derivDecl)
              hsc_env <- getSession
              (_, ic) <- liftIO $ hscParsedDecls hsc_env [noLoc derivDecl]
              setSession $ hsc_env { hsc_IC = ic }

            let tvs = map (getRdrName) (tyConTyVars tc)
            let tvbnds = userHsTyVarBndrs noSrcSpan tvs
            let targetInst = nlHsTyConApp targetableClsName
                             [nlHsTyConApp (getRdrName tc) (map nlHsTyVar tvs)]
            let instType = noLoc $ HsForAllTy Implicit Nothing
                           (HsQTvs [] tvbnds)
                           (noLoc (map (nlHsTyConApp targetableClsName . pure . nlHsTyVar) tvs))
                           targetInst
            let instDecl = InstD $ ClsInstD $ ClsInstDecl
                           instType emptyBag [] [] [] Nothing
            traceShowM (GHC.showPpr df instDecl)
            hsc_env <- getSession
            (_, ic) <- liftIO $ hscParsedDecls hsc_env [noLoc instDecl]
            setSession $ hsc_env { hsc_IC = ic }

          -- FIXME: HOW THE HELL DOES THIS BREAK THE PRINTER??!?!??!?!
          -- try using HscMain.hscCompileCoreExpr instead, the Core is easy to produce
          -- in this case, and avoids stupid name resolution crap
          -- hv <- compileExpr $ traceShowId
          --       ("Language.Haskell.Liquid.Model.Dict :: Language.Haskell.Liquid.Model.Dict (Test.Target.Targetable.Targetable ("++ showpp mt ++"))")
          hsc_env <- getSession

          let targetType = nlHsTyConApp targetableClsName [toHsType mt]

          let dictExpr = ExprWithTySig (nlHsVar dictDataName)
                                       (nlHsTyConApp dictTcName [targetType])
                                       PlaceHolder
          let dictStmt = noLoc $ LetStmt $ HsValBinds $ ValBindsIn
                         (listToBag [noLoc $
                                     mkFunBind (noLoc $ mkVarUnqual $ fsLit "_compile")
                                     [mkSimpleMatch [] (noLoc dictExpr)]])
                         []
          traceShowM (GHC.showPpr df dictStmt)
          x <- liftIO $ hscParsedStmt hsc_env dictStmt
          case x of
            Nothing -> return Nothing
            Just (_, hvals_io, _) -> do
              [hv] <- liftIO hvals_io
              traceShowM ("addDict", showpp mt)
              let d = TargetDict $ unsafeCoerce hv
              -- let d = TargetDict (Dict :: Dict (Targetable [Int]))
              return (Just (v, t, d))


monomorphize :: Type -> Type
monomorphize t = substTyWith tvs (replicate (length tvs) intTy) t
  where
  tvs = varSetElemsKvsFirst (tyVarsOfType t)

-- query :: Int -> SpecType -> Target Symbol
-- query d t = {- inModule mod . -} making sort $ do
--     xs <- queryCtors d t
--     x  <- fresh sort
--     oneOf x xs
--     constrain $ ofReft (reft t) (var x)
--     return x
--    where
--      -- mod  = symbol $ GHC.Generics.moduleName (undefined :: D1 c f a)
--      sort = FObj . symbol . showpp $ toType t

-- queryCtors :: Int -> SpecType -> Target [(Expr, Expr)]
-- queryCtors d t = undefined


hscParsedStmt :: HscEnv
              -> GhciLStmt RdrName  -- ^ The parsed statement
              -> IO ( Maybe ([Id]
                    , IO [HValue]
                    , FixityEnv))
hscParsedStmt hsc_env parsed_stmt = runInteractiveHsc hsc_env $ do

  -- Rename and typecheck it
  hsc_env <- getHscEnv
  (ids, tc_expr, fix_env) <- ioMsgMaybe $ tcRnStmt hsc_env parsed_stmt

  -- Desugar it
  ds_expr <- ioMsgMaybe $ deSugarExpr hsc_env tc_expr
  liftIO (lintInteractiveExpr "desugar expression" hsc_env ds_expr)
  handleWarnings

  -- Then code-gen, and link it
  -- It's important NOT to have package 'interactive' as thisPackageKey
  -- for linking, else we try to link 'main' and can't find it.
  -- Whereas the linker already knows to ignore 'interactive'
  let  src_span     = srcLocSpan interactiveSrcLoc
  hval <- liftIO $ hscCompileCoreExpr hsc_env src_span ds_expr
  let hval_io = unsafeCoerce# hval :: IO [HValue]

  return $ Just (ids, hval_io, fix_env)

  -- -- Rename and typecheck it
  -- (ids, tc_expr, fix_env) <- ioMsgMaybe $ tcRnStmt hsc_env stmt

  -- -- Desugar it
  -- ds_expr <- ioMsgMaybe $ deSugarExpr hsc_env tc_expr
  -- liftIO (lintInteractiveExpr "desugar expression" hsc_env ds_expr)
  -- handleWarnings

  -- -- Then code-gen, and link it
  -- -- It's important NOT to have package 'interactive' as thisUnitId
  -- -- for linking, else we try to link 'main' and can't find it.
  -- -- Whereas the linker already knows to ignore 'interactive'
  -- let src_span = srcLocSpan interactiveSrcLoc
  -- hval <- liftIO $ hscCompileCoreExpr hsc_env src_span ds_expr

  -- return $ Just (ids, hval, fix_env)
handleWarnings :: Hsc ()
handleWarnings = do
    dflags <- getDynFlags
    w <- getWarnings
    liftIO $ printOrThrowWarnings dflags w
    clearWarnings
ioMsgMaybe :: IO (Messages, Maybe a) -> Hsc a
ioMsgMaybe ioA = do
    ((warns,errs), mb_r) <- liftIO ioA
    logWarnings warns
    case mb_r of
        Nothing -> throwErrors errs
        Just r  -> return r
throwErrors :: ErrorMessages -> Hsc a
throwErrors = liftIO . throwIO . mkSrcErr
getWarnings :: Hsc WarningMessages
getWarnings = Hsc $ \_ w -> return (w, w)
clearWarnings :: Hsc ()
clearWarnings = Hsc $ \_ _ -> return ((), emptyBag)
logWarnings :: WarningMessages -> Hsc ()
logWarnings w = Hsc $ \_ w0 -> return ((), w0 `unionBags` w)

-- hscDeclsWithLocation :: HscEnv
--                      -> String -- ^ The statement
--                      -> String -- ^ The source
--                      -> Int    -- ^ Starting line
--                      -> IO ([TyThing], InteractiveContext)
hscParsedDecls hsc_env0 decls =
 runInteractiveHsc hsc_env0 $ do

    {- Rename and typecheck it -}
    hsc_env <- getHscEnv
    tc_gblenv <- ioMsgMaybe $ tcRnDeclsi hsc_env decls

    {- Grab the new instances -}
    -- We grab the whole environment because of the overlapping that may have
    -- been done. See the notes at the definition of InteractiveContext
    -- (ic_instances) for more details.
    let defaults = tcg_default tc_gblenv

    {- Desugar it -}
    -- We use a basically null location for iNTERACTIVE
    let iNTERACTIVELoc = ModLocation{ ml_hs_file   = Nothing,
                                      ml_hi_file   = Panic.panic "hsDeclsWithLocation:ml_hi_file",
                                      ml_obj_file  = Panic.panic "hsDeclsWithLocation:ml_hi_file"}
    ds_result <- hscDesugar' iNTERACTIVELoc tc_gblenv

    {- Simplify -}
    simpl_mg <- liftIO $ hscSimplify hsc_env ds_result

    {- Tidy -}
    (tidy_cg, mod_details) <- liftIO $ tidyProgram hsc_env simpl_mg

    let dflags = hsc_dflags hsc_env
        !CgGuts{ cg_module    = this_mod,
                 cg_binds     = core_binds,
                 cg_tycons    = tycons,
                 cg_modBreaks = mod_breaks } = tidy_cg

        !ModDetails { md_insts     = cls_insts
                    , md_fam_insts = fam_insts } = mod_details
            -- Get the *tidied* cls_insts and fam_insts

        data_tycons = filter isDataTyCon tycons

    {- Prepare For Code Generation -}
    -- Do saturation and convert to A-normal form
    prepd_binds <- {-# SCC "CorePrep" #-}
      liftIO $ corePrepPgm hsc_env iNTERACTIVELoc core_binds data_tycons

    {- Generate byte code -}
    cbc <- liftIO $ byteCodeGen dflags this_mod
                                prepd_binds data_tycons mod_breaks

    let src_span = srcLocSpan interactiveSrcLoc
    liftIO $ linkDecls hsc_env src_span cbc

    let tcs = filterOut isImplicitTyCon (mg_tcs simpl_mg)
        patsyns = mg_patsyns simpl_mg

        ext_ids = [ id | id <- bindersOfBinds core_binds
                       , isExternalName (idName id)
                       , not (isDFunId id || isImplicitId id) ]
            -- We only need to keep around the external bindings
            -- (as decided by TidyPgm), since those are the only ones
            -- that might be referenced elsewhere.
            -- The DFunIds are in 'cls_insts' (see Note [ic_tythings] in HscTypes
            -- Implicit Ids are implicit in tcs

        tythings =  map AnId ext_ids ++ map ATyCon tcs ++ map (AConLike . PatSynCon) patsyns

    let icontext = hsc_IC hsc_env
        ictxt    = extendInteractiveContext icontext ext_ids tcs
                                            cls_insts fam_insts defaults patsyns
    return (tythings, ictxt)

-- rttiEnvironment :: HscEnv -> IO HscEnv
-- rttiEnvironment hsc_env@HscEnv{hsc_IC=ic} = do
--    let tmp_ids = [id | AnId id <- ic_tythings ic]
--        incompletelyTypedIds =
--            [id | id <- tmp_ids
--                , not $ noSkolems id
--                , (occNameFS.nameOccName.idName) id /= result_fs]
--    hsc_env' <- foldM improveTypes hsc_env (map idName incompletelyTypedIds)
--    return hsc_env'
--     where
--      noSkolems = isEmptyVarSet . tyVarsOfType . idType
--      improveTypes hsc_env@HscEnv{hsc_IC=ic} name = do
--       let tmp_ids = [id | AnId id <- ic_tythings ic]
--           Just id = find (\i -> idName i == name) tmp_ids
--       if noSkolems id
--          then return hsc_env
--          else do
--            mb_new_ty <- reconstructType hsc_env 10 id
--            let old_ty = idType id
--            case mb_new_ty of
--              Nothing -> return hsc_env
--              Just new_ty -> do
--               case improveRTTIType hsc_env old_ty new_ty of
--                Nothing -> return $
--                         WARN(True, text (":print failed to calculate the "
--                                            ++ "improvement for a type")) hsc_env
--                Just subst -> do
--                  let dflags = hsc_dflags hsc_env
--                  when (dopt Opt_D_dump_rtti dflags) $
--                       printInfoForUser dflags alwaysQualify $
--                       fsep [text "RTTI Improvement for", ppr id, equals, ppr subst]

--                  let ic' = substInteractiveContext ic subst
--                  return hsc_env{hsc_IC=ic'}
