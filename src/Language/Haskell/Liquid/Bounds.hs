{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Bounds (

    Bound(..), 

    RBound, RRBound,

    RBEnv, RRBEnv,

    makeBound

	) where

import Text.PrettyPrint.HughesPJ

import Data.Hashable
import Data.Monoid
import Data.Bifunctor

import qualified Data.HashMap.Strict as M
import Control.Applicative                      ((<$>))

import Language.Fixpoint.Types
import Language.Fixpoint.Misc  (mapSnd)

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.RefType

data Bound t e = Bound { bname   :: LocSymbol    -- * The name of the bound
                       , bparams :: [(LocSymbol, t)]  -- * These are abstract refinements, for now
                       , bargs   :: [(LocSymbol, t)]  -- * These are value variables
                       , bbody   :: e            -- * The body of the bound
                       }	

type RBound     = RRBound RSort
type RRBound ty = Bound ty Pred

type RBEnv = M.HashMap LocSymbol RBound 
type RRBEnv ty = M.HashMap LocSymbol (RRBound ty) 


instance Hashable (Bound t e) where
	hashWithSalt i = hashWithSalt i . bname


instance (PPrint e) => (Show (Bound t e)) where
	show = showpp

instance (PPrint e) => (PPrint (Bound t e)) where
	pprint (Bound s ps xs e) =   text "bound" <+> pprint s <+> pprint (fst <$> ps) <+> text "=" <+>
	                             pprint_bsyms (fst <$> xs) <+> pprint e




instance Bifunctor Bound where
	first  f (Bound s ps xs e) = Bound s (mapSnd f <$> ps) (mapSnd f <$> xs) e
	second f (Bound s ps xs e) = Bound s ps xs (f e)


makeBound :: (PPrint r, UReftable r)
         => RRBound RSort -> [Symbol] -> (RRType r) -> (RRType r)
makeBound (Bound _ ps xs p) qs t 
  = RRTy [(dummySymbol, ct)] mempty OCons t
  where 
  	ct = foo (zip (val . fst <$> ps) qs) p xs

foo :: (PPrint r, UReftable r) => [(Symbol, Symbol)] -> Pred -> [(LocSymbol, RSort)] -> RRType r
foo penv (PImp p q) [(v, t)] 
  = RFun dummySymbol tp tq mempty
  where 
    t' = ofRSort t
    tp = t' `strengthen` makeRef penv v p   
    tq = t' `strengthen` makeRef penv v q 

foo penv (PImp z zs) ((x, t):xs)  
  = RFun (val x) t' (foo penv zs xs) mempty 
  where
  	t' = ofRSort t `strengthen` makeRef penv x z 

foo _ _ _ 
  = error "foo" -- NV TODO

makeRef :: (UReftable r) => [(Symbol, Symbol)] -> LocSymbol -> Pred -> r
makeRef penv v (PBexp (EApp p es)) | Just _ <- lookup (val p) penv  
  = ofUReft (U (Reft(val v, [])) r mempty)
  where EVar e = last es 
        es'    = init es 
        r      = Pr [PV q (PVProp ()) e (((), dummySymbol,) <$> es')]
        Just q = lookup (val p) penv

makeRef _ v p 
  = ofReft (Reft(val v, [RConc p]))
--   = ofReft ( U (Reft(val v, [])) (Pr [PV q (PVProp ()) (last es) es]) mempty)


pprint_bsyms [] = text ""
pprint_bsyms xs = text "\\" <+> pprint xs <+> text "->"

instance Eq (Bound t e) where
	b1 == b2 = (bname b1) == (bname b2)  


