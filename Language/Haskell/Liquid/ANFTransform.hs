{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}

-------------------------------------------------------------------------------------
------------ Code to convert Core to Administrative Normal Form ---------------------
-------------------------------------------------------------------------------------

module Language.Haskell.Liquid.ANFTransform (anormalize) where
import           Coercion (isCoVar, isCoVarType)
import           CoreSyn
import           CoreUtils                        (exprType)
import           DsMonad                          (DsM, initDs)
import           FastString                       (fsLit)
import           GHC                              hiding (exprType)
import           HscTypes
import           Id                               (mkSysLocalM)
import           Literal
import           MkCore                           (mkCoreLets)
import           Outputable                       (trace)
import           Var                              (varType, setVarType)
import           TypeRep
import           Type                             (mkForAllTys, substTy, mkForAllTys, mkTopTvSubst)
import           TyCon                            (tyConDataCons_maybe)
import           DataCon                          (dataConInstArgTys)
import           VarEnv                           (VarEnv, emptyVarEnv, extendVarEnv, lookupWithDefaultVarEnv)
import           Control.Monad
import           Control.Applicative              ((<$>))
import           Language.Fixpoint.Types (anfPrefix)
import           Language.Haskell.Liquid.GhcMisc  (MGIModGuts(..), showPpr)
import           Language.Fixpoint.Misc     (fst3, errorstar)
import           Data.Maybe                       (fromMaybe)
import           Data.List                        (sortBy, (\\))

anormalize :: HscEnv -> MGIModGuts -> IO [CoreBind]
anormalize hscEnv modGuts
  = do -- putStrLn "***************************** GHC CoreBinds ***************************" 
       -- putStrLn $ showPpr orig_cbs
       liftM (fromMaybe err . snd) $ initDs hscEnv m grEnv tEnv act 
    where m        = mgi_module modGuts
          grEnv    = mgi_rdr_env modGuts
          tEnv     = modGutsTypeEnv modGuts
          act      = liftM concat $ mapM (normalizeTopBind emptyVarEnv) orig_cbs
          orig_cbs = mgi_binds modGuts
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

normalizeTopBind γ (NonRec x e)
  = do e' <- stitch `fmap` normalize γ e
       return [normalizeTyVars $ NonRec x e']

normalizeTopBind γ (Rec xes)
  = liftM (map normalizeTyVars)(normalizeBind γ (Rec xes))

normalizeTyVars (NonRec x e) = NonRec (setVarType x t') e
  where t'       = subst msg as as' bt
        msg      = "WARNING unable to renameVars on " ++ showPpr x
        as'      = fst $ collectTyBinders e
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

------------------------------------------------------------------
normalizeBind :: VarEnv Id -> CoreBind -> DsM [CoreBind]
------------------------------------------------------------------

normalizeBind γ (NonRec x e)
   = do (bs, e') <- normalize γ e
        return (bs ++ [NonRec x e'])

normalizeBind γ (Rec xes)
  = do es' <- mapM (normalize γ >=> (return . stitch)) es
       return [Rec (zip xs es')]
    where (xs, es) = unzip xes

--------------------------------------------------------------------
normalizeName :: VarEnv Id -> CoreExpr -> DsM ([CoreBind], CoreExpr)
--------------------------------------------------------------------

-- normalizeNameDebug γ e 
--   = liftM (tracePpr ("normalizeName" ++ showPpr e)) $ normalizeName γ e

normalizeName _ e@(Lit (LitInteger _ _))
  = normalizeLiteral e

normalizeName _ e@(Tick _ (Lit (LitInteger _ _)))
  = normalizeLiteral e

normalizeName γ (Var x)
  = return ([], Var (lookupWithDefaultVarEnv γ x x))

normalizeName _ e@(Type _)
  = return ([], e)

normalizeName _ e@(Lit _)
  = return ([], e)

normalizeName γ e@(Coercion _)
  = do x        <- freshNormalVar $ exprType e
       return ([NonRec x e], Var x)

normalizeName γ (Tick n e)
  = do (bs, e') <- normalizeName γ e
       return (bs, Tick n e')

normalizeName γ e
  = do (bs, e') <- normalize γ e
       x        <- freshNormalVar $ exprType e
       return (bs ++ [NonRec x e'], Var x)

---------------------------------------------------------------------
normalizeLiteral :: CoreExpr -> DsM ([CoreBind], CoreExpr)
---------------------------------------------------------------------

normalizeLiteral e =
  do x <- freshNormalVar (exprType e)
     return ([NonRec x e], Var x)

freshNormalVar = mkSysLocalM (fsLit anfPrefix)

---------------------------------------------------------------------
normalize :: VarEnv Id -> CoreExpr -> DsM ([CoreBind], CoreExpr)
---------------------------------------------------------------------

normalize γ (Lam x e)
  = do e' <- stitch `fmap` normalize γ e
       return ([], Lam x e')

normalize γ (Let b e)
  = do bs'        <- normalizeBind γ b
       (bs'', e') <- normalize γ e
       return (bs' ++ bs'', e')
       -- Need to float bindings all the way up to the top 
       -- Due to GHCs odd let-bindings (see tests/pos/lets.hs) 

normalize γ (Case e x t as)
  = do (bs, n) <- normalizeName γ e
       x'      <- freshNormalVar τx -- rename "wild" to avoid shadowing
       let γ'   = extendVarEnv γ x x'
       as'     <- forM as $ \(c, xs, e') -> liftM ((c, xs,) . stitch) (normalize γ' e')
       as''    <- expandDefaultCase τx as' 
       return     (bs, Case n x' t as'')
    where τx = varType x

normalize γ (Var x)
  = return ([], Var (lookupWithDefaultVarEnv γ x x))

normalize _ e@(Lit _)
  = return ([], e)

normalize _ e@(Type _)
  = return ([], e)

normalize γ (Cast e τ)
  = do (bs, e') <- normalize γ e
       return (bs, Cast e' τ)

normalize γ (App e1 e2)
  = do (bs1, e1') <- normalize γ e1
       (bs2, n2 ) <- normalizeName γ e2
       return (bs1 ++ bs2, App e1' n2)

normalize γ (Tick n e)
  = do (bs, e') <- normalize γ e
       return (bs, Tick n e')

normalize _ (Coercion c) 
  = return ([], Coercion c)

stitch :: ([CoreBind], CoreExpr) -> CoreExpr
stitch (bs, e) = mkCoreLets bs e


----------------------------------------------------------------------------------
expandDefaultCase :: Type -> [(AltCon, [Id], CoreExpr)] -> DsM [(AltCon, [Id], CoreExpr)]
----------------------------------------------------------------------------------

expandDefaultCase (TyConApp tc argτs) z@((DEFAULT, _ ,e) : dcs)
  = case tyConDataCons_maybe tc of
       Just ds -> do let ds' = ds \\ [ d | (DataAlt d, _ , _) <- dcs] 
                     dcs'   <- forM ds' $ cloneCase argτs e
                     return $ sortCases $ dcs' ++ dcs
       Nothing -> return z --

expandDefaultCase _ z
   = return z

cloneCase argτs e d 
  = do xs  <- mapM freshNormalVar $ dataConInstArgTys d argτs
       return (DataAlt d, xs, e)

sortCases = sortBy (\x y -> cmpAltCon (fst3 x) (fst3 y))

