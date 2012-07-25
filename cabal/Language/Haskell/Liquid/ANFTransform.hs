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
          act      = liftM concat $ mapM normalizeBind orig_cbs
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
normalizeBind :: CoreBind -> DsM [CoreBind]
------------------------------------------------------------------

normalizeBind (NonRec x e) 
  = do (bs, e') <- normalize e
       return (bs ++ [NonRec x e'])
       
normalizeBind (Rec xes)
  = do es' <- mapM (normalize >=> (return . stitch)) es
       return [Rec (zip xs es')]
    where (xs, es) = unzip xes

---------------------------------------------------------------------------------------------
normalizeName, normalizeScrutinee, normalizeLiteral :: CoreExpr -> DsM ([CoreBind], CoreExpr)
---------------------------------------------------------------------------------------------

normalizeName_debug e = liftM (tracePpr ("normalizeName" ++ showPpr e)) $ normalizeName e

normalizeName e@(Lit (LitInteger _ _)) 
  = normalizeLiteral e 

normalizeName e@(Tick _ (Lit (LitInteger _ _))) 
  = normalizeLiteral e 

normalizeName e
  | isBase e
  = return ([], e)

normalizeName e@(Tick _ e')
  | isBase e'
  = return ([], e)

normalizeName e
  = do (bs, e') <- normalize e
       x        <- freshNormalVar (exprType e)
       return (bs ++ [NonRec x e'], Var x)

normalizeLiteral e = 
  do x <- freshNormalVar (exprType e)
     return ([NonRec x e], Var x)

normalizeScrutinee e 
  | isPrimitiveType (exprType e) 
  = return ([], e)
  | otherwise  
  = normalizeName e

freshNormalVar = mkSysLocalM (fsLit anfPrefix)

isBase (Var  _)   = True
isBase (Type _)   = True
isBase e@(Lit  _) = True
isBase _          = False


---------------------------------------------------------------------
normalize :: CoreExpr -> DsM ([CoreBind], CoreExpr)
---------------------------------------------------------------------

normalize (Lam x e)
  = do e' <- stitch `fmap` normalize e 
       return ([], Lam x e') 

normalize (Let b e)
  = do bs'        <- normalizeBind b
       (bs'', e') <- normalize e
       return (bs' ++ bs'', e')

normalize (Case e x t as)
  = do (bs, n) <- normalizeScrutinee e 
       as'     <- forM as $ \(c, xs, e) -> liftM ((c, xs,) . stitch) (normalize e)
       x'      <- freshNormalVar $ varType x -- rename "wild" to avoid shadowing
       return  $ (bs, Case n x' t as')

normalize e@(Var _)
  = return ([], e)

normalize e@(Lit _)
  = return ([], e)

normalize e@(Type _)
  = return ([], e)

normalize (Cast e τ)
  = do (bs, e') <- normalize e
       return (bs, Cast e' τ)

normalize (App e1 e2)
  = do (bs1, e1') <- normalize e1
       (bs2, n2 ) <- normalizeName e2
       return (bs1 ++ bs2, App e1' n2)

normalize (Tick n e)
  = do (bs, e') <- normalize e 
       return (bs, Tick n e') 

normalize e 
  = errorstar $ "normalize: TODO" ++ showPpr e

stitch :: ([CoreBind], CoreExpr) -> CoreExpr
stitch (bs, e) = tr_foldr' Let e bs
