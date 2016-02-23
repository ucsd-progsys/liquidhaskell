-- | This module contains the various instances for Subable,
--   which (should) depend on the visitors, and hence cannot
--   be in the same place as the @Term@ definitions.

module Language.Fixpoint.Types.Substitutions (
    mkSubst
  , isEmptySubst
  , substExcept
  , substfExcept
  , subst1Except
  , targetSubstSyms
  , filterSubst
  ) where

import           Data.Maybe
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types.Refinements
import           Language.Fixpoint.Misc
import           Text.PrettyPrint.HughesPJ
import           Text.Printf               (printf)

instance Monoid Subst where
  mempty  = emptySubst
  mappend = catSubst

filterSubst :: (Symbol -> Expr -> Bool) -> Subst -> Subst
filterSubst f (Su m) = Su (M.filterWithKey f m)

emptySubst :: Subst
emptySubst = Su M.empty

catSubst :: Subst -> Subst -> Subst
catSubst (Su s1) θ2@(Su s2) = Su $ M.union s1' s2
  where
    s1'                     = subst θ2 <$> s1

mkSubst :: [(Symbol, Expr)] -> Subst
mkSubst = Su . M.fromList . reverse

isEmptySubst :: Subst -> Bool
isEmptySubst (Su xes) = M.null xes

targetSubstSyms :: Subst -> [Symbol]
targetSubstSyms (Su ms) = syms $ M.elems ms

instance Subable () where
  syms _      = []
  subst _ ()  = ()
  substf _ () = ()
  substa _ () = ()

instance (Subable a, Subable b) => Subable (a,b) where
  syms  (x, y)   = syms x ++ syms y
  subst su (x,y) = (subst su x, subst su y)
  substf f (x,y) = (substf f x, substf f y)
  substa f (x,y) = (substa f x, substa f y)

instance Subable a => Subable [a] where
  syms   = concatMap syms
  subst  = map . subst
  substf = map . substf
  substa = map . substa

instance Subable a => Subable (M.HashMap k a) where
  syms   = syms . M.elems
  subst  = M.map . subst
  substf = M.map . substf
  substa = M.map . substa

subst1Except :: (Subable a) => [Symbol] -> a -> (Symbol, Expr) -> a
subst1Except xs z su@(x, _)
  | x `elem` xs = z
  | otherwise   = subst1 z su

substfExcept :: (Symbol -> Expr) -> [Symbol] -> Symbol -> Expr
substfExcept f xs y = if y `elem` xs then EVar y else f y

substExcept  :: Subst -> [Symbol] -> Subst
-- substExcept  (Su m) xs = Su (foldr M.delete m xs)
substExcept (Su xes) xs = Su $ M.filterWithKey (const . not . (`elem` xs)) xes

instance Subable Symbol where
  substa f                 = f
  substf f x               = subSymbol (Just (f x)) x
  subst su x               = subSymbol (Just $ appSubst su x) x -- subSymbol (M.lookup x s) x
  syms x                   = [x]

appSubst :: Subst -> Symbol -> Expr
appSubst (Su s) x = fromMaybe (EVar x) (M.lookup x s)

subSymbol (Just (EVar y)) _ = y
subSymbol Nothing         x = x
subSymbol a               b = errorstar (printf "Cannot substitute symbol %s with expression %s" (showFix b) (showFix a))

instance Subable Expr where
  syms                     = exprSymbols
  substa f                 = substf (EVar . f)
  substf f (EApp s e)      = EApp (substf f s) (substf f e)
  substf f (ENeg e)        = ENeg (substf f e)
  substf f (EBin op e1 e2) = EBin op (substf f e1) (substf f e2)
  substf f (EIte p e1 e2)  = EIte (substf f p) (substf f e1) (substf f e2)
  substf f (ECst e so)     = ECst (substf f e) so
  substf f (EVar x)        = f x
  substf f (PAnd ps)       = PAnd $ map (substf f) ps
  substf f (POr  ps)       = POr  $ map (substf f) ps
  substf f (PNot p)        = PNot $ substf f p
  substf f (PImp p1 p2)    = PImp (substf f p1) (substf f p2)
  substf f (PIff p1 p2)    = PIff (substf f p1) (substf f p2)
  substf f (PAtom r e1 e2) = PAtom r (substf f e1) (substf f e2)
  substf _ p@(PKVar _ _)   = p
  substf _  (PAll _ _)     = errorstar "substf: FORALL"
  substf _  p              = p


  subst su (EApp f e)      = EApp (subst su f) (subst su e)
  subst su (ENeg e)        = ENeg (subst su e)
  subst su (EBin op e1 e2) = EBin op (subst su e1) (subst su e2)
  subst su (EIte p e1 e2)  = EIte (subst su p) (subst su e1) (subst su e2)
  subst su (ECst e so)     = ECst (subst su e) so
  subst su (EVar x)        = appSubst su x
  subst su (PAnd ps)       = PAnd $ map (subst su) ps
  subst su (POr  ps)       = POr  $ map (subst su) ps
  subst su (PNot p)        = PNot $ subst su p
  subst su (PImp p1 p2)    = PImp (subst su p1) (subst su p2)
  subst su (PIff p1 p2)    = PIff (subst su p1) (subst su p2)
  subst su (PAtom r e1 e2) = PAtom r (subst su e1) (subst su e2)
  subst su (PKVar k su')   = PKVar k $ su' `catSubst` su
  subst _  (PAll _ _)      = errorstar "subst: FORALL"
  subst su (PExist bs p)
          | disjoint su bs = PExist bs $ subst su p --(substExcept su (fst <$> bs)) p
          | otherwise      = errorstar "subst: EXISTS (without disjoint binds)"
  subst _  p               = p

disjoint :: Subst -> [(Symbol, Sort)] -> Bool
disjoint (Su su) bs = S.null $ suSyms `S.intersection` bsSyms
  where
    suSyms = S.fromList $ syms (M.elems su) ++ syms (M.keys su)
    bsSyms = S.fromList $ syms $ fst <$> bs

instance Monoid Expr where
  mempty      = PTrue
  mappend p q = pAnd [p, q]
  mconcat     = pAnd

instance Monoid Reft where
  mempty  = trueReft
  mappend = meetReft

meetReft :: Reft -> Reft -> Reft
meetReft (Reft (v, ra)) (Reft (v', ra'))
  | v == v'          = Reft (v , ra  `mappend` ra')
  | v == dummySymbol = Reft (v', ra' `mappend` (ra `subst1`  (v , EVar v')))
  | otherwise        = Reft (v , ra  `mappend` (ra' `subst1` (v', EVar v )))

instance Monoid SortedReft where
  mempty        = RR mempty mempty
  mappend t1 t2 = RR (mappend (sr_sort t1) (sr_sort t2)) (mappend (sr_reft t1) (sr_reft t2))

instance Subable Reft where
  syms (Reft (v, ras))      = v : syms ras
  substa f (Reft (v, ras))  = Reft (f v, substa f ras)
  subst su (Reft (v, ras))  = Reft (v, subst (substExcept su [v]) ras)
  substf f (Reft (v, ras))  = Reft (v, substf (substfExcept f [v]) ras)
  subst1 (Reft (v, ras)) su = Reft (v, subst1Except [v] ras su)

instance Subable SortedReft where
  syms               = syms . sr_reft
  subst su (RR so r) = RR so $ subst su r
  substf f (RR so r) = RR so $ substf f r
  substa f (RR so r) = RR so $ substa f r

instance Reftable () where
  isTauto _ = True
  ppTy _  d = d
  top  _    = ()
  bot  _    = ()
  meet _ _  = ()
  toReft _  = mempty
  ofReft _  = mempty
  params _  = []

instance Reftable Reft where
  isTauto  = all isTautoPred . conjuncts . reftPred
  ppTy     = pprReft
  toReft   = id
  ofReft   = id
  params _ = []
  bot    _        = falseReft
  top (Reft(v,_)) = Reft (v, mempty)

pprReft (Reft (v, p)) d
  | isTautoPred p
  = d
  | otherwise
  = braces (toFix v <+> colon <+> d <+> text "|" <+> ppRas [p])

instance Reftable SortedReft where
  isTauto  = isTauto . toReft
  ppTy     = ppTy . toReft
  toReft   = sr_reft
  ofReft   = errorstar "No instance of ofReft for SortedReft"
  params _ = []
  bot s    = s { sr_reft = falseReft }

-- RJ: this depends on `isTauto` hence, here.
instance PPrint Reft where
  pprint r
    | isTauto r        = text "true"
    | otherwise        = pprintReft r

instance PPrint SortedReft where
  pprint (RR so (Reft (v, ras)))
    = braces
    $ pprint v <+> text ":" <+> toFix so <+> text "|" <+> pprint ras


instance Fixpoint Reft where
  toFix = pprReftPred

instance Fixpoint SortedReft where
  toFix (RR so (Reft (v, ra)))
    = braces
    $ toFix v <+> text ":" <+> toFix so <+> text "|" <+> toFix (conjuncts ra)

instance Show Reft where
  show = showFix

instance Show SortedReft where
  show  = showFix

pprReftPred (Reft (_, p))
  | isTautoPred p
  = text "true"
  | otherwise
  = ppRas [p]

ppRas = cat . punctuate comma . map toFix . flattenRefas

--------------------------------------------------------------------------------
-- | TODO: Rewrite using visitor -----------------------------------------------
--------------------------------------------------------------------------------

exprSymbols :: Expr -> [Symbol]
exprSymbols = go
  where
    go (EVar x)           = [x]
    go (EApp f e)         = go f ++ go e
    go (ENeg e)           = go e
    go (EBin _ e1 e2)     = go e1 ++ go e2
    go (EIte p e1 e2)     = exprSymbols p ++ go e1 ++ go e2
    go (ECst e _)         = go e
    go (PAnd ps)          = concatMap go ps
    go (POr ps)           = concatMap go ps
    go (PNot p)           = go p
    go (PIff p1 p2)       = go p1 ++ go p2
    go (PImp p1 p2)       = go p1 ++ go p2
    go (PAtom _ e1 e2)    = exprSymbols e1 ++ exprSymbols e2
    go (PKVar _ (Su su))  = {- CUTSOLVER k : -} syms (M.elems su)
    go (PAll xts p)       = (fst <$> xts) ++ go p
    go _                  = []
