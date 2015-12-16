{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Types.Bounds (

    Bound(..),

    RBound, RRBound,

    RBEnv, RRBEnv,

    makeBound,
    envToSub

        ) where

import Text.PrettyPrint.HughesPJ

import Data.List (partition)
import Data.Maybe
import Data.Hashable
import Data.Monoid
import Data.Bifunctor

import qualified Data.HashMap.Strict as M
import Control.Applicative           ((<$>))

import Language.Fixpoint.Types
import Language.Fixpoint.Misc        (errorstar)

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Misc  (mapFst, mapSnd)
import Language.Haskell.Liquid.Types.RefType


data Bound t e
  = Bound { bname   :: LocSymbol         -- ^ The name of the bound
          , tyvars  :: [t]               -- ^ Type variables that appear in the bounds
          , bparams :: [(LocSymbol, t)]  -- ^ These are abstract refinements, for now
          , bargs   :: [(LocSymbol, t)]  -- ^ These are value variables
          , bbody   :: e                 -- ^ The body of the bound
          }

type RBound        = RRBound RSort
type RRBound tv    = Bound tv Pred

type RBEnv         = M.HashMap LocSymbol RBound
type RRBEnv tv     = M.HashMap LocSymbol (RRBound tv)


instance Hashable (Bound t e) where
        hashWithSalt i = hashWithSalt i . bname

instance Eq (Bound t e) where
  b1 == b2 = (bname b1) == (bname b2)

instance (PPrint e, PPrint t) => (Show (Bound t e)) where
        show = showpp


instance (PPrint e, PPrint t) => (PPrint (Bound t e)) where
        pprint (Bound s vs ps xs e) =   text "bound" <+> pprint s <+>
                                        text "forall" <+> pprint vs <+> text "." <+>
                                        pprint (fst <$> ps) <+> text "=" <+>
                                        pprint_bsyms (fst <$> xs) <+> pprint e

pprint_bsyms [] = text ""
pprint_bsyms xs = text "\\" <+> pprint xs <+> text "->"

instance Bifunctor Bound where
        first  f (Bound s vs ps xs e) = Bound s (f <$> vs) (mapSnd f <$> ps) (mapSnd f <$> xs) e
        second f (Bound s vs ps xs e) = Bound s vs ps xs (f e)


makeBound :: (PPrint r, UReftable r)
          => RRBound RSort -> [RRType r] -> [Symbol] -> (RRType r) -> (RRType r)
makeBound (Bound _  vs ps xs p) ts qs t
  = RRTy cts mempty OCons t
  where
    cts  = (\(x, t) -> (x, foldr subsTyVar_meet t su)) <$> cts'

    cts' = makeBoundType penv rs xs

    penv = zip (val . fst <$> ps) qs
    rs   = bkImp [] p

    bkImp acc (PImp p q) = bkImp (p:acc) q
    bkImp acc p          = p:acc

    su  = [(α, toRSort t, t) | (RVar α _, t) <-  zip vs ts ]

makeBoundType :: (PPrint r, UReftable r)
              => [(Symbol, Symbol)]
              -> [Pred]
              -> [(LocSymbol, RSort)]
              -> [(Symbol, RRType r)]
makeBoundType penv (q:qs) xts = go xts
  where
    -- NV TODO: Turn this into a proper error
    go [] = errorstar "Bound with empty symbols"

    go [(x, t)]      = [(dummySymbol, tp t x), (dummySymbol, tq t x)]
    go ((x, t):xtss) = (val x, mkt t x):(go xtss)

    mkt t x = ofRSort t `strengthen` ofUReft (U (Reft (val x, mempty))
                                                (Pr $ M.lookupDefault [] (val x) ps) mempty)
    tp t x  = ofRSort t `strengthen` ofUReft (U (Reft (val x, pAnd rs))
                                                (Pr $ M.lookupDefault [] (val x) ps) mempty)
    tq t x  = ofRSort t `strengthen` makeRef penv x q

    (ps, rs) = partitionPs penv qs


-- NV TODO: Turn this into a proper error
makeBoundType _ _ _           = errorstar "Bound with empty predicates"


partitionPs :: [(Symbol, Symbol)] -> [Pred] -> (M.HashMap Symbol [UsedPVar], [Pred])
partitionPs penv qs = mapFst makeAR $ partition (isPApp penv) qs
  where
    makeAR ps       = M.fromListWith (++) $ map (toUsedPVars penv) ps

isPApp penv (PBexp (EApp p _))  = isJust $ lookup (val p) penv
isPApp _    _                   = False

toUsedPVars penv q@(PBexp (EApp _ es)) = (x, [toUsedPVar penv q])
  where
    -- NV : TODO make this a better error
    x = (\(EVar x) -> x) $ last es
toUsedPVars _ _ = error "This cannot happen"

toUsedPVar penv (PBexp (EApp p es))
  = PV q (PVProp ()) e (((), dummySymbol,) <$> es')
   where
     EVar e = last es
     es'    = init es
     Just q = lookup (val p) penv

toUsedPVar _ _ = error "This cannot happen"

envToSub = go []
  where
    go _   []              = error "This cannot happen: envToSub on 0 elems"
    go _   [(_,_)]         = error "This cannot happen: envToSub on 1 elem"
    go ack [(_,l), (_, r)] = (reverse ack, l, r)
    go ack (x:xs)          = go (x:ack) xs

-- `makeRef` is used to make the refinement of the last implication,
-- thus it can contain both concrete and abstract refinements

makeRef :: (UReftable r) => [(Symbol, Symbol)] -> LocSymbol -> Pred -> r
makeRef penv v (PAnd rs) = ofUReft (U (Reft (val v, pAnd rrs)) r mempty)
  where
    r                    = Pr  (toUsedPVar penv <$> pps)
    (pps, rrs)           = partition (isPApp penv) rs

makeRef penv v rr
  | isPApp penv rr       = ofUReft (U (Reft(val v, mempty)) r mempty)
  where
    r                    = Pr [toUsedPVar penv rr]

makeRef _    v p         = ofReft (Reft(val v, p))
