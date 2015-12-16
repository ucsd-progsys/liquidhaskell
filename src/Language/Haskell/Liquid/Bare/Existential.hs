module Language.Haskell.Liquid.Bare.Existential (
    txExpToBind
  ) where

import Control.Applicative ((<$>))
import Control.Monad.State
import Data.Char

import qualified Data.HashMap.Strict as M

import Language.Fixpoint.Misc (errorstar, fst3)
import Language.Fixpoint.Types.Names (headSym)
import Language.Fixpoint.Types (Expr(..), Symbol, symbol, exprReft)

import Language.Haskell.Liquid.Types.RefType (strengthen, uTop)
import Language.Haskell.Liquid.Types

-------------------------------------------------------------------------------
-- | Replace Predicate Arguments With Existentials ----------------------------
-------------------------------------------------------------------------------

data ExSt = ExSt { fresh :: Int
                 , emap  :: M.HashMap Symbol (RSort, Expr)
                 , pmap  :: M.HashMap Symbol RPVar
                 }

-- | Niki: please write more documentation for this, maybe an example?
-- I can't really tell whats going on... (RJ)

txExpToBind   :: SpecType -> SpecType
txExpToBind t = evalState (expToBindT t) (ExSt 0 M.empty πs)
  where πs = M.fromList [(pname p, p) | p <- ty_preds $ toRTypeRep t ]

expToBindT :: SpecType -> State ExSt SpecType
expToBindT (RVar v r)
  = expToBindRef r >>= addExists . RVar v
expToBindT (RFun x t1 t2 r)
  = do t1' <- expToBindT t1
       t2' <- expToBindT t2
       expToBindRef r >>= addExists . RFun x t1' t2'
expToBindT (RAllT a t)
  = liftM (RAllT a) (expToBindT t)
expToBindT (RAllP p t)
  = liftM (RAllP p) (expToBindT t)
expToBindT (RAllS s t)
  = liftM (RAllS s) (expToBindT t)
expToBindT (RApp c ts rs r)
  = do ts' <- mapM expToBindT ts
       rs' <- mapM expToBindReft rs
       expToBindRef r >>= addExists . RApp c ts' rs'
expToBindT (RAppTy t1 t2 r)
  = do t1' <- expToBindT t1
       t2' <- expToBindT t2
       expToBindRef r >>= addExists . RAppTy t1' t2'
expToBindT (RRTy xts r o t)
  = do xts' <- zip xs <$> mapM expToBindT ts
       r'   <- expToBindRef r
       t'   <- expToBindT t
       return $ RRTy xts' r' o t'
  where
     (xs, ts) = unzip xts
expToBindT t
  = return t

expToBindReft              :: SpecProp -> State ExSt SpecProp
expToBindReft (RProp s t)  = RProp s  <$> expToBindT t
expToBindReft (RPropP s r) = RPropP s <$> expToBindRef r
expToBindReft (RHProp _ _) = errorstar "TODO:EFFECTS:expToBindReft"

getBinds :: State ExSt (M.HashMap Symbol (RSort, Expr))
getBinds
  = do bds <- emap <$> get
       modify $ \st -> st{emap = M.empty}
       return bds

addExists t = liftM (M.foldlWithKey' addExist t) getBinds

addExist t x (tx, e) = REx x t' t
  where t' = (ofRSort tx) `strengthen` uTop r
        r  = exprReft e

expToBindRef :: UReft r -> State ExSt (UReft r)
expToBindRef (U r (Pr p) l)
  = mapM expToBind p >>= return . (\p -> U r p l). Pr

expToBind :: UsedPVar -> State ExSt UsedPVar
expToBind p
  = do Just π <- liftM (M.lookup (pname p)) (pmap <$> get)
       let pargs0 = zip (pargs p) (fst3 <$> pargs π)
       pargs' <- mapM expToBindParg pargs0
       return $ p{pargs = pargs'}

expToBindParg :: (((), Symbol, Expr), RSort) -> State ExSt ((), Symbol, Expr)
expToBindParg ((t, s, e), s') = liftM ((,,) t s) (expToBindExpr e s')

expToBindExpr :: Expr ->  RSort -> State ExSt Expr
expToBindExpr e@(EVar s) _ | isLower $ headSym $ symbol s
  = return e
expToBindExpr e t
  = do s <- freshSymbol
       modify $ \st -> st{emap = M.insert s (t, e) (emap st)}
       return $ EVar s

freshSymbol :: State ExSt Symbol
freshSymbol
  = do n <- fresh <$> get
       modify $ \s -> s{fresh = n+1}
       return $ symbol $ "ex#" ++ show n
