{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Haskell.Liquid.RefSplit (

	splitXRelatedRefs

	) where

import Control.Applicative
import Data.List (partition)
import Text.PrettyPrint.HughesPJ

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.PrettyPrint ()

import Language.Fixpoint.Types 
import Language.Fixpoint.Misc 

splitXRelatedRefs :: Symbol -> SpecType -> (SpecType, SpecType)
splitXRelatedRefs x t = splitRType x t
   


splitRType f (RVar a r) = (RVar a r1, RVar a r2)
  where
  	(r1, r2) = splitRef f r

splitRType f (RFun x tx t r) = (RFun x tx1 t1 r1, RFun x tx2 t2 r2) 
  where
  	(tx1, tx2) = splitRType f tx
  	(t1,  t2)  = splitRType f t
  	(r1,  r2)  = splitRef   f r

splitRType f (RAllT v t) = (RAllT v t1, RAllT v t2)
  where
  	(t1, t2) = splitRType f t 

splitRType f (RAllP p t) = (RAllP p t1, RAllP p t2)
  where
  	(t1, t2) = splitRType f t

splitRType f (RAllS s t) = (RAllS s t1, RAllS s t2)
  where
  	(t1, t2) = splitRType f t


splitRType f (RApp c ts rs r) = (RApp c ts1 rs1 r1, RApp c ts2 rs2 r2)
  where
  	(ts1, ts2) = unzip (splitRType f <$> ts)
  	(rs1, rs2) = unzip (splitUReft f <$> rs)
  	(r1,  r2)  = splitRef f r 

splitRType f (RAllE x tx t) = (RAllE x tx1 t1, RAllE x tx2 t2)
  where
  	(tx1, tx2) = splitRType f tx
  	(t1, t2)   = splitRType f t

splitRType f (REx x tx t) = (REx x tx1 t1, REx x tx2 t2)
  where
  	(tx1, tx2) = splitRType f tx
  	(t1, t2)   = splitRType f t

splitRType _ (RExprArg e) = (RExprArg e, RExprArg e)

splitRType f (RAppTy tx t r) = (RAppTy tx1 t1 r1, RAppTy tx2 t2 r2)
  where
  	(tx1, tx2) = splitRType f tx
  	(t1,  t2)  = splitRType f t
  	(r1,  r2)  = splitRef   f r

splitRType f (RRTy xs r o t) = (RRTy xs1 r1 o t1, RRTy xs2 r2 o t2)
  where
  	(xs1, xs2) = unzip (go <$> xs)
  	(r1, r2) = splitRef   f r 
  	(t1, t2) = splitRType f t

  	go (x, t) = let (t1, t2) = splitRType f t in ((x,t1), (x, t2))


splitRType f (RHole r) = (RHole r1, RHole r2)
  where
  	(r1, r2) = splitRef f r 

splitUReft :: Symbol -> RTProp c tv (UReft Reft) -> (RTProp c tv (UReft Reft), RTProp c tv (UReft Reft))
splitUReft x (RPropP xs r) = (RPropP xs r1, RPropP xs r2)
  where 
  	(r1, r2) = splitRef x r

splitUReft x (RProp xs t) = (RProp xs t1, RProp xs t2)
  where 
  	(t1, t2) = splitRType x t

splitUReft _ (RHProp xs _) = (RHProp xs w1, RHProp xs w2)
  where 
  	(w1, w2) = error "TODO: RefSplit.splitUReft"

splitRef f (U r p s) = (U r1 p1 s, U r2 p2 s)
	where
		(r1, r2) = splitReft f r 
		(p1, p2) = splitPred f p

splitReft f (Reft (v, Refa xs)) = (Reft (v, Refa $ pAnd xs1), Reft (v, Refa $ pAnd xs2))
  where
    (xs1, xs2)       = partition (isFree f) (unPAnd xs)

    unPAnd (PAnd ps) = concatMap unPAnd ps 
    unPAnd p         = [p]

splitPred f (Pr ps) = (Pr ps1, Pr ps2)
  where
    (ps1, ps2) = partition g ps
    g p = any (isFree f) (thd3 <$> pargs p) 	


class IsFree a where
	isFree :: Symbol -> a -> Bool

instance (Subable x) => (IsFree x) where
	isFree x p = x `elem` syms p

instance Show (UReft Reft) where
	 show = render . pprint
