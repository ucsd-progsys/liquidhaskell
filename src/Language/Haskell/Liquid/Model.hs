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
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.Liquid.Model where

import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Bifunctor
import qualified Data.HashMap.Strict                   as HM
import           Data.Proxy
import           GHC.Prim
import           System.Console.CmdArgs.Verbosity (whenLoud)
import           Text.PrettyPrint.HughesPJ
import           Text.Printf
import           Unsafe.Coerce

import           Language.Fixpoint.Types (FixResult(..), mapPredReft, Symbol, symbol, Expr(..),
                                          mkSubst, subst)
import           Language.Fixpoint.Smt.Interface
import           Language.Fixpoint.Types.Config (SMTSolver)
import           Language.Haskell.Liquid.GHC.Interface
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types         hiding (var)
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.UX.Tidy

import           Test.Target.Monad
import           Test.Target.Targetable
import           Test.Target.Testable


import           Bag
import           GHC hiding (obtainTermFromVal)
import qualified Outputable as GHC
import           DynFlags
import           HscMain
import           InstEnv
import           OccName
import           RdrName
import           Type
import           TysWiredIn
import           Var
import           InteractiveEval

import Id
import ByteCodeGen      ( byteCodeGen )
import Linker
import CoreLint         ( lintInteractiveExpr )
import Panic
import ConLike
import CoreSyn
import SrcLoc
import TcRnDriver
import TcRnMonad
import Desugar
import TidyPgm
import CorePrep
import TyCon
import ErrUtils
import HscTypes
import FastString
import Exception
import Util

-- import           Debug.Trace

getModels :: GhcInfo -> Config -> FixResult Error -> IO (FixResult Error)
getModels info cfg fi = case fi of
  Unsafe cs
    | cfg `hasOpt` counterExamples
    -> fmap Unsafe . runLiquidGhc mbenv cfg $ do
    df <- getSessionDynFlags
    let df' = df { packageFlags = ExposePackage (PackageArg "liquidhaskell")
                                  (ModRenaming True [])
                                : packageFlags df
                 }
    _ <- setSessionDynFlags df'
    imps <- getContext
    setContext ( IIModule (targetMod info)
               : IIDecl ((simpleImportDecl (mkModuleName "Test.Target.Targetable"))
                                           { ideclQualified = True })
               : imps)
    mapM (getModel info cfg) cs
  _         -> return fi
  where
  mbenv = Just (env info)

getModel :: GhcInfo -> Config -> Error -> Ghc Error
getModel info cfg err
  = getModel' info cfg err
    `gcatch`
    \(e :: SomeException) -> do
      liftIO $ whenLoud $
        printf "WARNING: could not generate counter-example: %s\n" (show e)
      return err

getModel' :: GhcInfo -> Config -> Error -> Ghc Error
getModel' info _cfg (ErrSubType { pos, msg, ctx, tact, texp }) = do
  let vv  = (symbol "VV", tact `strengthen` (fmap (mapPredReft PNot) (rt_reft texp)))
  let vts = vv : HM.toList ctx

  vtds <- addDicts vts

  hsc_env <- getSession
  df <- getDynFlags
  let opts = defaultOpts
  model <- liftIO $ withContext False False (solver opts) (target info) $ \smt -> do
    runTarget opts (initState (target info) (spec info) smt) $ do
      free <- gets freesyms
      let dcs = [ (v, tidySymbol v)
                | iv <- impVars info
                , isDataConId iv
                , let v = symbol iv
                ]
      let su  = mkSubst $ map (second EVar) (free ++ dcs)
      n <- asks depth
      vs <- forM vtds $ \(v, t, md) -> case md of
        Nothing -> do
          -- if we don't have a Targetable instance, just encode it as an Int so
          -- the name is available
          addVariable (v, getType (Proxy :: Proxy Int))
          return v
        Just (TargetDict d@Dict)  -> do
          addVariable (v, getType (dictProxy d))
          query (dictProxy d) n v (subst su t)
      setup
      _ <- liftIO $ command smt CheckSat
      forM (zip vs vtds) $ \(sv, (v, t, md)) -> case md of
        Nothing -> do return (v, NoModel t)
        Just (TargetDict d@Dict) -> do
          x <- decode sv t
          xt <- liftIO $ obtainTermFromVal hsc_env 100 True (toType t) (x `asTypeOfDict` d)
          return (v, WithModel (text (GHC.showPpr df xt)) t)

  let (_, WithModel vv_model _) : ctx_model = model
  return (ErrSubTypeModel
          { pos  = pos
          , msg  = msg
          , ctxM  = HM.fromList ctx_model --  `HM.union` fmap NoModel ctx
                   -- HM.union is *left-biased*
          , tactM = WithModel vv_model tact
          , texp = texp
          })

getModel' _ _ err = return err

withContext :: Bool -> Bool -> SMTSolver -> FilePath -> (Context -> IO a) -> IO a
withContext l ho smt t act = do
  ctx <- makeContext l ho smt t
  act ctx `finally` cleanupContext ctx

dictProxy :: forall t. Dict (Targetable t) -> Proxy t
dictProxy Dict = Proxy

asTypeOfDict :: forall t. t -> Dict (Targetable t) -> t
x `asTypeOfDict` Dict = x

data Dict :: Constraint -> * where
  Dict :: a => Dict a

data TargetDict = forall t. TargetDict (Dict (Targetable t))

addDicts :: [(Symbol, SpecType)] -> Ghc [(Symbol, SpecType, Maybe TargetDict)]
addDicts bnds = mapM addDict bnds

-- TODO: instead of returning Maybe (Symbol, SpecType, TargetDict),
-- return (Symbol, SpecType, Maybe TargetDict).
-- if Nothing, generate a binder for the value, but no skeleton / model.
-- this way we can possibly still generate models for other values in the context
addDict :: (Symbol, SpecType) -> Ghc (Symbol, SpecType, Maybe TargetDict)
addDict (v, t) = addDict' (v, t) `gcatch` \(_e :: SomeException) -> return (v, t, Nothing)

addDict' :: (Symbol, SpecType) -> Ghc (Symbol, SpecType, Maybe TargetDict)
addDict' (v, t) = do
  let mt = monomorphize (toType t)
  -- traceShowM (v, t, showPpr mt)
  case tyConAppTyCon_maybe mt of
    Nothing -> return (v, t, Nothing)
    Just tc | isClassTyCon tc || isFunTyCon tc || isPrimTyCon tc
              || isPromotedDataCon tc || isPromotedTyCon tc
              -- FIXME: shouldn't be necessary..
              -- why do we have binders for higher-kinded types??
              || Type.isFunTy (Type.typeKind mt)
              -- TODO: cannot handle `Targetable (Fix f)`, see higher-kinded classes e.g. Eq1, Ord1, etc...
              || any Type.isFunTy (map Var.varType (tyConTyVars tc))
              -> return (v, t, Nothing)
    Just tc -> do
      getInfo False (getName tc) >>= \case
        Nothing -> return (v, t, Nothing)
        Just (ATyCon tc, _, cis, _) -> do
          genericsMod   <- lookupModule (mkModuleName "GHC.Generics") Nothing
          targetableMod <- lookupModule (mkModuleName "Test.Target.Targetable") Nothing
          modelMod      <- lookupModule (mkModuleName "Language.Haskell.Liquid.Model") Nothing

          let genericClsName    = mkOrig genericsMod (mkClsOcc "Generic")
          let targetableClsName = mkOrig targetableMod (mkClsOcc "Targetable")
          let dictTcName        = mkOrig modelMod (mkTcOcc "Dict")
          let dictDataName      = mkOrig modelMod (mkDataOcc "Dict")

          -- let mt = monomorphize (toType t)

          -- liftIO $ putStrLn $ showPpr tc
          -- maybe add a Targetable instance
          unless ("Test.Target.Targetable.Targetable"
                  `elem` map (showpp.is_cls_nm) cis) $ do

            let tvs =  map (getRdrName) (tyConTyVars tc)
            let tvbnds = userHsTyVarBndrs noSrcSpan tvs

            -- maybe derive a Generic instance
            unless ("GHC.Generics.Generic"
                    `elem` map (showpp.is_cls_nm) cis) $ do
              let genericInst = nlHsTyConApp genericClsName
                               [nlHsTyConApp (getRdrName tc) (map nlHsTyVar tvs)]
              let instType = noLoc $ HsForAllTy Implicit Nothing
                             (HsQTvs [] tvbnds)
                             (noLoc []) -- (noLoc (map (nlHsTyConApp genericClsName . pure . nlHsTyVar) tvs))
                             genericInst
              let derivDecl = DerivD $ DerivDecl instType Nothing
              -- liftIO $ putStrLn $ showPpr derivDecl
              hsc_env <- getSession
              (_, ic) <- liftIO $ hscParsedDecls hsc_env [noLoc derivDecl]
              setSession $ hsc_env { hsc_IC = ic }

            let targetInst = nlHsTyConApp targetableClsName
                             [nlHsTyConApp (getRdrName tc) (map nlHsTyVar tvs)]
            let instType = noLoc $ HsForAllTy Implicit Nothing
                           (HsQTvs [] tvbnds)
                           -- (noLoc [])
                           (noLoc (map (nlHsTyConApp targetableClsName . pure . nlHsTyVar) tvs))
                           targetInst
            let instDecl = InstD $ ClsInstD $ ClsInstDecl
                           instType emptyBag [] [] [] Nothing
            -- liftIO $ putStrLn $ showPpr instDecl
            hsc_env <- getSession
            (_, ic) <- liftIO $ hscParsedDecls hsc_env [noLoc instDecl]
            setSession $ hsc_env { hsc_IC = ic }

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
          -- liftIO $ putStrLn $ showPpr dictStmt
          x <- liftIO $ hscParsedStmt hsc_env dictStmt
          case x of
            Nothing -> return (v, t, Nothing)
            Just (_, hvals_io, _) -> do
              [hv] <- liftIO hvals_io
              let d = TargetDict $ unsafeCoerce hv
              return (v, t, Just d)

        _ -> return (v, t, Nothing)

-- FIXME: can't instantiate higher-kinded tvs with 'Int'
monomorphize :: Type -> Type
monomorphize t = substTyWith tvs (replicate (length tvs) intTy) t
  where
  tvs = varSetElemsKvsFirst (tyVarsOfType t)


----------------------------------------------------------------------
-- Slightly altered from GHC
----------------------------------------------------------------------

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
hscParsedDecls :: HscEnv
               -> [LHsDecl RdrName] -> IO ([TyThing], InteractiveContext)
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
