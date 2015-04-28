{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}

-------------------------------------------------------------------------------------
------------ Code to convert Core to Administrative Normal Form ---------------------
-------------------------------------------------------------------------------------

module Language.Haskell.Liquid.ANFTransform (anormalize) where
import           CoreSyn
import           CoreUtils                        (exprType)
import qualified DsMonad
import           DsMonad                          (initDs)
import           GHC                              hiding (exprType)
import           HscTypes
import           Id                               (mkSysLocalM)
import           Literal
import           MkCore                           (mkCoreLets)
import           Outputable                       (trace)
import           Var                              (varType, setVarType)
import           TypeRep
import           Type                             (mkForAllTys, substTy, mkForAllTys, mkTopTvSubst, isTyVar)
import           TyCon                            (tyConDataCons_maybe)
import           DataCon                          (dataConInstArgTys)
import           FamInstEnv                       (emptyFamInstEnv)
import           VarEnv                           (VarEnv, emptyVarEnv, extendVarEnv, lookupWithDefaultVarEnv)
import           Control.Monad.State.Lazy
import           UniqSupply                       (MonadUnique)
import           Language.Fixpoint.Types (anfPrefix)
import           Language.Haskell.Liquid.GhcMisc  (MGIModGuts(..), showPpr, symbolFastString)
import           Language.Haskell.Liquid.TransformRec
import           Language.Fixpoint.Misc     (fst3, errorstar)
import           Data.Maybe                       (fromMaybe)
import           Data.List                        (sortBy, (\\))
import           Control.Applicative

anormalize :: Bool -> HscEnv -> MGIModGuts -> IO [CoreBind]
anormalize expandFlag hscEnv modGuts
  = do -- putStrLn "***************************** GHC CoreBinds ***************************" 
       -- putStrLn $ showPpr orig_cbs
       liftM (fromMaybe err . snd) $ initDs hscEnv m grEnv tEnv emptyFamInstEnv act
    where m        = mgi_module modGuts
          grEnv    = mgi_rdr_env modGuts
          tEnv     = modGutsTypeEnv modGuts
          act      = liftM concat $ mapM (normalizeTopBind expandFlag emptyVarEnv) orig_cbs
          orig_cbs = transformRecExpr $ mgi_binds modGuts
          err      = errorstar "anormalize fails!"

modGutsTypeEnv mg = typeEnvFromEntities ids tcs fis
  where ids = bindersOfBinds (mgi_binds mg)
        tcs = mgi_tcs mg
        fis = mgi_fam_insts mg

------------------------------------------------------------------
----------------- Actual Normalizing Functions -------------------
------------------------------------------------------------------

-- Can't make the below default for normalizeBind as it 
-- fails tests/pos/lets.hs due to GHCs odd let-bindings

normalizeTopBind :: Bool -> VarEnv Id -> Bind CoreBndr -> DsMonad.DsM [CoreBind]
normalizeTopBind expandFlag γ (NonRec x e)
  = do e' <- runDsM $ evalStateT (stitch γ e) (DsST expandFlag  [])
       return [normalizeTyVars $ NonRec x e']

normalizeTopBind expandFlag γ (Rec xes)
  = do xes' <- runDsM $ execStateT (normalizeBind γ (Rec xes)) (DsST expandFlag [])
       return $ map normalizeTyVars (st_binds xes')

normalizeTyVars (NonRec x e) = NonRec (setVarType x t') $ normalizeForAllTys e
  where t'       = subst msg as as' bt
        msg      = "WARNING unable to renameVars on " ++ showPpr x
        as'      = fst $ splitForAllTys $ exprType e
        (as, bt) = splitForAllTys (varType x)
normalizeTyVars (Rec xes)    = Rec xes'
  where nrec = normalizeTyVars <$> ((\(x, e) -> NonRec x e) <$> xes)
        xes' = (\(NonRec x e) -> (x, e)) <$> nrec

subst msg as as' bt
  | length as == length as'
  = mkForAllTys as' $ substTy su bt
  | otherwise
  = trace msg $ mkForAllTys as bt
  where su = mkTopTvSubst $ zip as (mkTyVarTys as')

-- | eta-expand CoreBinds with quantified types
normalizeForAllTys :: CoreExpr -> CoreExpr
normalizeForAllTys e = case e of
  Lam b _ | isTyVar b
    -> e
  _ -> mkLams tvs (mkTyApps e (map mkTyVarTy tvs))
  where
  (tvs, _) = splitForAllTys (exprType e)


newtype DsM a = DsM {runDsM :: DsMonad.DsM a}
   deriving (Functor, Monad, MonadUnique, Applicative)

data DsST = DsST { st_expandflag :: Bool
                 , st_binds      :: [CoreBind]
                 }

type DsMW = StateT DsST DsM

------------------------------------------------------------------
normalizeBind :: VarEnv Id -> CoreBind -> DsMW ()
------------------------------------------------------------------

normalizeBind γ (NonRec x e)
   = do e' <- normalize γ e
        add [NonRec x e']

normalizeBind γ (Rec xes)
  = do es' <- mapM (stitch γ) es
       add [Rec (zip xs es')]
    where (xs, es) = unzip xes

--------------------------------------------------------------------
normalizeName :: VarEnv Id -> CoreExpr -> DsMW CoreExpr
--------------------------------------------------------------------

-- normalizeNameDebug γ e 
--   = liftM (tracePpr ("normalizeName" ++ showPpr e)) $ normalizeName γ e

normalizeName _ e@(Lit (LitInteger _ _))
  = normalizeLiteral e

normalizeName _ e@(Tick _ (Lit (LitInteger _ _)))
  = normalizeLiteral e

normalizeName γ (Var x)
  = return $ Var (lookupWithDefaultVarEnv γ x x)

normalizeName _ e@(Type _)
  = return e

normalizeName _ e@(Lit _)
  = return e

normalizeName _ e@(Coercion _)
  = do x     <- lift $ freshNormalVar $ exprType e
       add  [NonRec x e]
       return $ Var x

normalizeName γ (Tick n e)
  = do e'    <- normalizeName γ e
       return $ Tick n e'

normalizeName γ e
  = do e'   <- normalize γ e
       x    <- lift $ freshNormalVar $ exprType e
       add [NonRec x e']
       return $ Var x


add :: [CoreBind] -> DsMW ()
add w = modify $ \s -> s{st_binds = st_binds s++w}

---------------------------------------------------------------------
normalizeLiteral :: CoreExpr -> DsMW CoreExpr
---------------------------------------------------------------------

normalizeLiteral e =
  do x <- lift $ freshNormalVar (exprType e)
     add [NonRec x e]
     return $ Var x

freshNormalVar :: Type -> DsM Id
freshNormalVar = mkSysLocalM (symbolFastString anfPrefix)

---------------------------------------------------------------------
normalize :: VarEnv Id -> CoreExpr -> DsMW CoreExpr
---------------------------------------------------------------------

normalize γ (Lam x e)
  = do e' <- stitch γ e
       return $ Lam x e'

normalize γ (Let b e)
  = do normalizeBind γ b
       normalize γ e
       -- Need to float bindings all the way up to the top 
       -- Due to GHCs odd let-bindings (see tests/pos/lets.hs) 

normalize γ (Case e x t as)
  = do n     <- normalizeName γ e
       x'    <- lift $ freshNormalVar τx -- rename "wild" to avoid shadowing
       let γ' = extendVarEnv γ x x'
       as'   <- forM as $ \(c, xs, e') -> liftM (c, xs,) (stitch γ' e')
       flag  <- st_expandflag <$> get
       as''  <- lift $ expandDefaultCase flag τx as' 
       return $ Case n x' t as''
    where τx = varType x

normalize γ (Var x)
  = return $ Var (lookupWithDefaultVarEnv γ x x)

normalize _ e@(Lit _)
  = return e

normalize _ e@(Type _)
  = return e

normalize γ (Cast e τ)
  = do e'    <- normalizeName γ e
       return $ Cast e' τ

normalize γ (App e1 e2)
  = do e1' <- normalize γ e1
       n2  <- normalizeName γ e2
       return $ App e1' n2

normalize γ (Tick n e)
  = do e' <- normalize γ e
       return $ Tick n e'

normalize _ (Coercion c) 
  = return $ Coercion c

stitch :: VarEnv Id -> CoreExpr -> DsMW CoreExpr 
stitch γ e
  = do bs'   <- get
       modify $ \s -> s {st_binds = []}
       e'    <- normalize γ e
       bs    <- st_binds <$> get
       put bs'
       return $ mkCoreLets bs e'

----------------------------------------------------------------------------------
expandDefaultCase :: Bool -> Type -> [(AltCon, [Id], CoreExpr)] -> DsM [(AltCon, [Id], CoreExpr)]
----------------------------------------------------------------------------------

expandDefaultCase flag tyapp zs@((DEFAULT, _ ,_) : _) | flag
  = expandDefaultCase' tyapp zs

expandDefaultCase _    tyapp@(TyConApp tc _) z@((DEFAULT, _ ,_):dcs)
  = case tyConDataCons_maybe tc of
       Just ds -> do let ds' = ds \\ [ d | (DataAlt d, _ , _) <- dcs] 
                     if (length ds') == 1 
                      then expandDefaultCase' tyapp z 
                      else return z
       Nothing -> return z --

expandDefaultCase _ _ z
   = return z

expandDefaultCase' (TyConApp tc argτs) z@((DEFAULT, _ ,e) : dcs)
  = case tyConDataCons_maybe tc of
       Just ds -> do let ds' = ds \\ [ d | (DataAlt d, _ , _) <- dcs] 
                     dcs'   <- forM ds' $ cloneCase argτs e
                     return $ sortCases $ dcs' ++ dcs
       Nothing -> return z --
expandDefaultCase' _ z
   = return z

cloneCase argτs e d 
  = do xs  <- mapM freshNormalVar $ dataConInstArgTys d argτs
       return (DataAlt d, xs, e)

sortCases = sortBy (\x y -> cmpAltCon (fst3 x) (fst3 y))

