{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}

-------------------------------------------------------------------------------------
------------ Code to convert Core to Administrative Normal Form ---------------------
-------------------------------------------------------------------------------------

module Language.Haskell.Liquid.ANFTransform (anormalize) where

import           CoreSyn
import           CoreUtils                        (exprType)
import           DsMonad                          (DsM, initDs)
import           FastString                       (fsLit)
import           GHC                              hiding (exprType)
import           HscTypes
import           Id                               (mkSysLocalM)
import           Literal
import           MkCore                           (mkCoreLets)
import           Outputable
import           Var                              (varType)
import           VarEnv                           (VarEnv, emptyVarEnv, extendVarEnv, lookupWithDefaultVarEnv)
import           Control.Monad
import           Language.Haskell.Liquid.Fixpoint (anfPrefix)
import           Language.Haskell.Liquid.GhcMisc  (MGIModGuts(..))
import           Language.Haskell.Liquid.Misc     (errorstar)
import           Data.Maybe                       (fromMaybe)

anormalize :: HscEnv -> MGIModGuts -> IO [CoreBind]
anormalize hscEnv modGuts
  = liftM (fromMaybe err . snd) $ initDs hscEnv m grEnv tEnv act 
    where m        = mgi_module modGuts
          grEnv    = mgi_rdr_env modGuts
          tEnv     = modGutsTypeEnv modGuts
          act      = liftM concat $ mapM (normalizeBind emptyVarEnv) orig_cbs
          orig_cbs = {- tracePpr "********** GHC Corebinds ********* \n" $ -} mgi_binds modGuts
          err      = errorstar "anormalize fails!"

modGutsTypeEnv mg = typeEnvFromEntities ids tcs fis
  where ids = bindersOfBinds (mgi_binds mg)
        tcs = mgi_tcs mg
        fis = mgi_fam_insts mg


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
  = do es' <- mapM (normalize γ >=> (return . stitch)) es
       return [Rec (zip xs es')]
    where (xs, es) = unzip xes

-------------------------------------------------------------------------------------
normalizeName :: VarEnv Id -> CoreExpr -> DsM ([CoreBind], CoreExpr)
-------------------------------------------------------------------------------------

-- normalizeNameDebug γ e = liftM (tracePpr ("normalizeName" ++ showPpr e)) $ normalizeName γ e

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

-- normalizeName _ e@(Tick n e')
  -- | isBase e'
  -- = return ([], e)

normalizeName γ (Tick n e)
  = do (bs, e') <- normalizeName γ e
       return (bs, Tick n e')

normalizeName γ e
  = do (bs, e') <- normalize γ e
       x        <- freshNormalVar $ exprType e
       return (bs ++ [NonRec x e'], Var x)

-- normalizeScrutinee γ e
--   | isPrimitiveType (exprType e)
--   = return ([], e)
--   | otherwise
--   = normalizeName γ e


-------------------------------------------------------------------------------------
normalizeLiteral :: CoreExpr -> DsM ([CoreBind], CoreExpr)
-------------------------------------------------------------------------------------

normalizeLiteral e =
  do x <- freshNormalVar (exprType e)
     return ([NonRec x e], Var x)

freshNormalVar = mkSysLocalM (fsLit anfPrefix)

-- isBase (Var  _)   = True
--isBase (Type _)   = True
--isBase e@(Lit  _) = True
--isBase _          = False


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
  = do (bs, n) <- {- normalizeScrutinee -} normalizeName γ e
       x'      <- freshNormalVar $ varType x -- rename "wild" to avoid shadowing
       let γ'   = extendVarEnv γ x x'
       as'     <- forM as $ \(c, xs, e') -> liftM ((c, xs,) . stitch) (normalize γ' e')
       return     (bs, Case n x' t as')

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

normalize _ e
  = errorstar $ "normalize: TODO" ++ showPpr e

stitch :: ([CoreBind], CoreExpr) -> CoreExpr
stitch (bs, e) = mkCoreLets bs e -- tr_foldr' Let e bs
