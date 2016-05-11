{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Language.Haskell.Liquid.Types.Bounds (

    Bound(..),

    RBound, RRBound,

    RBEnv, RRBEnv,

    makeBound,

    ) where

import Prelude hiding (error)
import Text.PrettyPrint.HughesPJ

import Data.List (partition)
import Data.Maybe
import Data.Hashable
-- import Data.Monoid
import Data.Bifunctor
import Data.Data

import qualified Data.HashMap.Strict as M
-- import Control.Applicative           ((<$>))

import Language.Fixpoint.Types

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Misc  (mapFst, mapSnd)
import Language.Haskell.Liquid.Types.RefType


data Bound t e
  = Bound { bname   :: LocSymbol         -- ^ The name of the bound
          , tyvars  :: [t]               -- ^ Type variables that appear in the bounds
          , bparams :: [(LocSymbol, t)]  -- ^ These are abstract refinements, for now
          , bargs   :: [(LocSymbol, t)]  -- ^ These are value variables
          , bbody   :: e                 -- ^ The body of the bound
          } deriving (Data, Typeable)

type RBound        = RRBound RSort
type RRBound tv    = Bound tv Expr

type RBEnv         = M.HashMap LocSymbol RBound
type RRBEnv tv     = M.HashMap LocSymbol (RRBound tv)


instance Hashable (Bound t e) where
  hashWithSalt i = hashWithSalt i . bname

instance Eq (Bound t e) where
  b1 == b2 = bname b1 == bname b2

instance (PPrint e, PPrint t) => (Show (Bound t e)) where
  show = showpp


instance (PPrint e, PPrint t) => (PPrint (Bound t e)) where
  pprintTidy k (Bound s vs ps xs e) = "bound" <+> pprintTidy k s <+>
                                      "forall" <+> pprintTidy k vs <+> "." <+>
                                      pprintTidy k (fst <$> ps) <+> "=" <+>
                                      ppBsyms k (fst <$> xs) <+> pprintTidy k e
    where
      ppBsyms _ [] = ""
      ppBsyms k xs = "\\" <+> pprintTidy k xs <+> "->"

instance Bifunctor Bound where
  first  f (Bound s vs ps xs e) = Bound s (f <$> vs) (mapSnd f <$> ps) (mapSnd f <$> xs) e
  second f (Bound s vs ps xs e) = Bound s vs ps xs (f e)

makeBound :: (PPrint r, UReftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r)
          => RRBound RSort -> [RRType r] -> [Symbol] -> RRType r -> RRType r
makeBound (Bound _  vs ps xs p) ts qs
         = RRTy cts mempty OCons
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
              -> [Expr]
              -> [(LocSymbol, RSort)]
              -> [(Symbol, RRType r)]
makeBoundType penv (q:qs) xts = go xts
  where
    -- NV TODO: Turn this into a proper error
    go [] = panic Nothing "Bound with empty symbols"

    go [(x, t)]      = [(dummySymbol, tp t x), (dummySymbol, tq t x)]
    go ((x, t):xtss) = (val x, mkt t x) : go xtss

    mkt t x = ofRSort t `strengthen` ofUReft (MkUReft (Reft (val x, mempty))
                                                (Pr $ M.lookupDefault [] (val x) ps) mempty)
    tp t x  = ofRSort t `strengthen` ofUReft (MkUReft (Reft (val x, pAnd rs))
                                                (Pr $ M.lookupDefault [] (val x) ps) mempty)
    tq t x  = ofRSort t `strengthen` makeRef penv x q

    (ps, rs) = partitionPs penv qs


-- NV TODO: Turn this into a proper error
makeBoundType _ _ _           = panic Nothing "Bound with empty predicates"


partitionPs :: [(Symbol, Symbol)] -> [Expr] -> (M.HashMap Symbol [UsedPVar], [Expr])
partitionPs penv qs = mapFst makeAR $ partition (isPApp penv) qs
  where
    makeAR ps       = M.fromListWith (++) $ map (toUsedPVars penv) ps

isPApp :: [(Symbol, a)] -> Expr -> Bool
isPApp penv (EApp (EVar p) _)  = isJust $ lookup p penv
isPApp penv (EApp e _)         = isPApp penv e
isPApp _    _                  = False

toUsedPVars :: [(Symbol, Symbol)] -> Expr -> (Symbol, [PVar ()])
toUsedPVars penv q@(EApp _ e) = (x, [toUsedPVar penv q])
  where
    -- NV : TODO make this a better error
    x = case unProp e of {EVar x -> x; e -> todo Nothing ("Bound fails in " ++ show e) }
toUsedPVars _ _ = impossible Nothing "This cannot happen"

unProp :: Expr -> Expr
unProp (EApp (EVar f) e)
  | f == propConName
  = e
unProp e
  = e

toUsedPVar :: [(Symbol, Symbol)] -> Expr -> PVar ()
toUsedPVar penv ee@(EApp _ _)
  = PV q (PVProp ()) e (((), dummySymbol,) <$> es')
   where
     EVar e = unProp $ last es
     es'    = init es
     Just q = lookup p penv
     (EVar p, es) = splitEApp ee

toUsedPVar _ _ = impossible Nothing "This cannot happen"

-- `makeRef` is used to make the refinement of the last implication,
-- thus it can contain both concrete and abstract refinements

makeRef :: (UReftable r) => [(Symbol, Symbol)] -> LocSymbol -> Expr -> r
makeRef penv v (PAnd rs) = ofUReft (MkUReft (Reft (val v, pAnd rrs)) r mempty)
  where
    r                    = Pr  (toUsedPVar penv <$> pps)
    (pps, rrs)           = partition (isPApp penv) rs

makeRef penv v rr
  | isPApp penv rr       = ofUReft (MkUReft (Reft(val v, mempty)) r mempty)
  where
    r                    = Pr [toUsedPVar penv rr]

makeRef _    v p         = ofReft (Reft(val v, p))
