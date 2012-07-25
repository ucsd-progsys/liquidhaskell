{-# LANGUAGE NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections #-}

-------------------------------------------------------------------------------------
------------ Code to convert Core to Administrative Normal Form ---------------------
-------------------------------------------------------------------------------------

module Language.Haskell.Liquid.ANFTransform (anormalize) where

import GHC		hiding 	(exprType)
import CoreUtils 		(exprType)
import Outputable
import CoreSyn
import HscTypes
import Literal
import DsMonad			(DsM, initDs)
import Id               (mkSysLocalM)
import FastString       (fsLit)
import Type             (isPrimitiveType)
import Var              (varType)
import VarEnv           (VarEnv, emptyVarEnv, extendVarEnv, lookupWithDefaultVarEnv)

import Control.Monad
import Language.Haskell.Liquid.Misc (traceShow)
import Language.Haskell.Liquid.Fixpoint                 (anfPrefix)
import Language.Haskell.Liquid.Misc (errorstar, tr_foldr')
import Language.Haskell.Liquid.GhcMisc (tracePpr)

anormalize :: HscEnv -> ModGuts -> IO [CoreBind]
anormalize hscEnv modGuts 
  = do (msgs, maybeCbs) <- initDs hscEnv mod grEnv tEnv act
       case maybeCbs of
         Just cbs -> return cbs
         Nothing  -> pprPanic "anormalize fails!" (empty)
    where mod      = mg_module modGuts
          grEnv    = mg_rdr_env modGuts
          tEnv     = modGutsTypeEnv modGuts
          act      = liftM concat $ mapM (normalizeBind emptyVarEnv) orig_cbs
          orig_cbs = {- tracePpr "********** GHC Corebinds ********* \n" $ -} mg_binds modGuts 


modGutsTypeEnv :: ModGuts -> TypeEnv
modGutsTypeEnv mg = typeEnvFromEntities ids tcs fis
  where ids = bindersOfBinds (mg_binds mg)
        tcs = mg_tcs mg
        fis = mg_fam_insts mg


------------------------------------------------------------------
----------------- Actual Normalizing Functions -------------------
------------------------------------------------------------------

------------------------------------------------------------------
normalizeBind :: VarEnv Id -> CoreBind -> DsM [CoreBind]
------------------------------------------------------------------

normalizeBind γ (NonRec x e) 
  = do (bs, e') <- normalize γ e
       return (bs ++ [NonRec x e'])
       
normalizeBind γ (Rec xes)
  = do es' <- mapM ((normalize γ) >=> (return . stitch)) es
       return [Rec (zip xs es')]
    where (xs, es) = unzip xes

-------------------------------------------------------------------------------------
normalizeName, normalizeScrutinee :: VarEnv Id -> CoreExpr -> DsM ([CoreBind], CoreExpr)
-------------------------------------------------------------------------------------

normalizeName_debug γ e = liftM (tracePpr ("normalizeName" ++ showPpr e)) $ normalizeName γ e

normalizeName _ e@(Lit (LitInteger _ _)) 
  = normalizeLiteral e 

normalizeName _ e@(Tick _ (Lit (LitInteger _ _))) 
  = normalizeLiteral e 

normalizeName _ e
  | isBase e
  = return ([], e)

normalizeName _ e@(Tick _ e')
  | isBase e'
  = return ([], e)

normalizeName γ e
  = do (bs, e') <- normalize γ e
       x        <- freshNormalVar $ exprType e
       return (bs ++ [NonRec x e'], Var x)

normalizeScrutinee γ e 
  | isPrimitiveType (exprType e) 
  = return ([], e)
  | otherwise  
  = normalizeName γ e


-------------------------------------------------------------------------------------
normalizeLiteral :: CoreExpr -> DsM ([CoreBind], CoreExpr)
-------------------------------------------------------------------------------------

normalizeLiteral e = 
  do x <- freshNormalVar (exprType e)
     return ([NonRec x e], Var x)

freshNormalVar = mkSysLocalM (fsLit anfPrefix)

isBase (Var  _)   = True
isBase (Type _)   = True
isBase e@(Lit  _) = True
isBase _          = False


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

normalize γ (Case e x t as)
  = do (bs, n) <- normalizeScrutinee γ e 
       x'      <- freshNormalVar $ varType x -- rename "wild" to avoid shadowing
       let γ'   = extendVarEnv γ x x'
       as'     <- forM as $ \(c, xs, e) -> liftM ((c, xs,) . stitch) (normalize γ' e)
       return  $ (bs, Case n x' t as')

normalize γ e@(Var x)
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

normalize _ e 
  = errorstar $ "normalize: TODO" ++ showPpr e

stitch :: ([CoreBind], CoreExpr) -> CoreExpr
stitch (bs, e) = tr_foldr' Let e bs
