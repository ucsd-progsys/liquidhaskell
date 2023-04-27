{-# LANGUAGE FlexibleInstances    #-}

-- Syntactic Equality of Types up tp forall type renaming

module Language.Haskell.Liquid.Types.Equality where 

import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Types
import qualified Liquid.GHC.API as Ghc

import Control.Monad.Writer.Lazy
-- import Control.Monad
import qualified Data.List as L

instance REq SpecType where 
  t1 =*= t2 = compareRType t1 t2 
  
compareRType :: SpecType -> SpecType -> Bool 
compareRType i1 i2 = res && unify ys
  where 
    unify vs = and (sndEq <$> L.groupBy (\(x1,_) (x2,_) -> x1 == x2) vs) 
    sndEq [] = True 
    sndEq [_] = True 
    sndEq ((_,y):xs) = all (==y) (snd <$> xs)

    (res, ys) = runWriter (go i1 i2)
    go :: SpecType -> SpecType -> Writer [(RTyVar, RTyVar)] Bool  
    go (RAllT x1 t1 r1) (RAllT x2 t2 r2)
      | RTV v1 <- ty_var_value x1
      , RTV v2 <- ty_var_value x2 
      , r1 =*= r2
      = go t1 (subt (v2, Ghc.mkTyVarTy v1) t2) 

    go (RVar v1 r1) (RVar v2 r2) 
      = do tell [(v1, v2)]
           return (r1 =*= r2) 
     -- = v1 == v2 && r1 =*= r2 
    go (RFun x1 _ t11 t12 r1) (RFun x2 _ t21 t22 r2)
      | x1 == x2 && r1 =*= r2
      = liftM2 (&&) (go t11 t21) (go t12 t22)
    go (RImpF x1 _ t11 t12 r1) (RImpF x2 _ t21 t22 r2)
      | x1 == x2    && r1 =*= r2
      = liftM2 (&&) (go t11 t21) (go t12 t22)    
    go (RAllP x1 t1) (RAllP x2 t2)
      | x1 == x2 
      = go t1 t2 
    go (RApp x1 ts1 ps1 r1) (RApp x2 ts2 ps2 r2)
      | x1 == x2 &&  
        r1 =*= r2 && and (zipWith (=*=) ps1 ps2) 
      = and <$> zipWithM go ts1 ts2
    go (RAllE x1 t11 t12) (RAllE x2 t21 t22) | x1 == x2 
      = liftM2 (&&) (go t11 t21) (go t12 t22) 
    go (REx x1 t11 t12) (REx x2 t21 t22) | x1 == x2
      = liftM2 (&&) (go t11 t21) (go t12 t22)
    go (RExprArg e1) (RExprArg e2)
      = return (e1 =*= e2) 
    go (RAppTy t11 t12 r1) (RAppTy t21 t22 r2) | r1 =*= r2 
      = liftM2 (&&) (go t11 t21) (go t12 t22)  
    go (RRTy _ _ _ r1) (RRTy _ _ _ r2) 
      = return (r1 =*= r2)
    go (RHole r1) (RHole r2)
      = return (r1 =*= r2)  
    go _t1 _t2 
      = return False 

class REq a where 
  (=*=) :: a -> a -> Bool 

instance REq t2 => REq (Ref t1 t2) where
    (RProp _ t1) =*= (RProp _ t2) = t1 =*= t2 

instance REq (UReft F.Reft) where
  (MkUReft r1 p1) =*= (MkUReft r2 p2)
     = r1 =*= r2 && p1 == p2
  
instance REq F.Reft where 
  F.Reft (v1, e1) =*= F.Reft (v2, e2) = F.subst1 e1 (v1, F.EVar v2) =*= e2 

instance REq F.Expr where 
  e1 =*= e2 = go (F.simplify e1) (F.simplify e2)
    where go r1 r2 = F.notracepp ("comparing " ++ showpp (F.toFix r1, F.toFix r2)) $ r1 == r2 

instance REq r => REq (Located r) where 
  t1 =*= t2 = val t1 =*= val t2         
  