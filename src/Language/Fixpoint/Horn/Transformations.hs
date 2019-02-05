module Language.Fixpoint.Horn.Transformations (
  poke,
  elim
) where

import           Language.Fixpoint.Horn.Types
import qualified Language.Fixpoint.Types      as F
import           Control.Monad (void)

-- |
-- >>> import Language.Fixpoint.Parse
-- >>> import Language.Fixpoint.Horn.Parse
-- >>> (q, opts) <- parseFromFile hornP "tests/horn/pos/ebind01.smt2"
-- >>> qCstr (poke q)
-- (and (forall ((m int) (true)) (and (forall ((x1 int) (and (true) (x1 x1))) (and (forall ((v int) (v == m + 1)) ((v == x1))) (forall ((v int) (v == x1 + 1)) ((v == 2 + m))))) (exists ((x1 int) (and (true) (x1 x1))) ((true))))))
-- >>> (q, opts) <- parseFromFile hornP "tests/horn/pos/ebind02.smt2"
-- >>> qCstr (poke q)
-- (and (forall ((m int) (true)) (forall ((z int) (z == m - 1)) (and (forall ((v1 int) (v1 == z + 2)) ((k v1))) (and (forall ((x1 int) (and (true) (x1 x1))) (and (forall ((v2 int) (k v2)) ((v2 == x1))) (forall ((v3 int) (v3 == x1 + 1)) ((v3 == m + 2))))) (exists ((x1 int) (and (true) (x1 x1))) ((true))))))))

------------------------------------------------------------------------------
poke :: Query a -> Query ()
------------------------------------------------------------------------------
poke (Query quals vars cstr) = Query quals (map void vars ++ pivars) (pokec cstr)
  where pivars = ebs cstr

ebs :: Cstr a -> [Var ()]
ebs (Head _ _) = []
ebs (CAnd cs) = ebs =<< cs
ebs (All _ c) = ebs c
ebs (Any (Bind x t _) c) = HVar x [t] () : ebs c

pokec :: Cstr a -> Cstr ()
pokec (Head c _) = (Head c ())
pokec (CAnd c) = CAnd (pokec <$> c)
pokec (All b c2) = All b $ pokec c2
pokec (Any b c2) = CAnd [All b' $ pokec c2, Any b' (Head (Reft F.PTrue) ())]
  -- TODO: actually use the renamer?
  where
    Bind x t p = b
    b' = Bind x t (PAnd [p, pi])
    pi = Var x [x]

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- Now, we have two options: either we can trust that KVars are solved in
-- topological order (which is impossible in general, or we create
-- disjunctive versions of Cstr and Pred, and go back and forth.

elim :: Cstr a -> Cstr a
elim c = dstr2cstr $ foldl elim1 d (boundKvars c) 
  where d = cstr2dstr c

elim1 :: Dstr a -> (F.Symbol,[F.Symbol]) -> Dstr a
elim1 c (k,xs) = doelim k (sol1 [] (k,xs) c) c

sol1 :: [Dind] -> (F.Symbol, [F.Symbol]) -> Dstr a -> ([Dind], Dred)
sol1 bs k (DAnd cs) = (concat (bs:bss), DPOr ps)
  where (bss, ps) = unzip $ sol1 [] k <$> cs
sol1 bs k (DAll b c) = (b:bs', c')
  where (bs', c') = sol1 bs k c
sol1 bs (k,xs) (DHead (DVar k' ys) _) | k == k'
  = (bs, DReft $ F.PAnd $ zipWith (F.PAtom F.Eq) (F.EVar <$> xs) (F.EVar <$> ys))
sol1 bs _ (DHead _ _) = (bs, DReft F.PFalse)
-- sol1 _ _ (Any _ _) =  error "ebinds don't work with old elim"

doelim :: F.Symbol -> ([Dind], Dred) -> Dstr a -> Dstr a
doelim k bp (DAnd cs)
  = DAnd $ doelim k bp <$> cs
doelim k (bs, p) (DAll (Dind x t (DVar k' _)) c)
  | k == k'
  = foldr DAll (DAll (Dind x t p) $ doelim k (bs,p) c) bs
doelim k bp (DAll b c)
  = DAll b (doelim k bp c)
doelim k _ (DHead (DVar k' _) a)
  | k == k'
  = DHead (DReft F.PTrue) a
doelim _ _ (DHead p a) = DHead p a
-- doelim _ _ (Any _ _) =  error "ebinds don't work with old elim"

boundKvars :: Cstr a -> [(F.Symbol,[F.Symbol])]
boundKvars (Head _ _) = []
boundKvars (CAnd c) = boundKvars =<< c
boundKvars (All (Bind _ _ (Var k xs)) c) = (k, xs) : boundKvars c
boundKvars (All _ c) = boundKvars c
boundKvars (Any (Bind _ _ (Var k xs)) c) = (k, xs) : boundKvars c
boundKvars (Any _ c) = boundKvars c

-------------------------------------------------------------------------------
-- | @Dred@ is a disjunctive predicate
-------------------------------------------------------------------------------
data Dred 
  = DReft  !F.Expr                               -- ^ r 
  | DVar   !F.Symbol ![F.Symbol]                 -- ^ $k(y1..yn) 
  | DPAnd  ![Dred]                               -- ^ p1 /\ .../\ pn 
  | DPOr   ![Dred]                               -- ^ p1 \/ ...\/ pn 
   
-------------------------------------------------------------------------------
-- | @Dstr@ is a disjunctive NNF Horn Constraint. 
-------------------------------------------------------------------------------
data Dind = Dind 
  { _dSym  :: !F.Symbol 
  , _dSort :: !F.Sort 
  , _dPred :: !Dred 
  }

data Dstr a
  = DHead  !Dred a               -- ^ p
  | DAnd   ![Dstr a]             -- ^ c1 /\ ... /\ cn
  | DAll   !Dind  !(Dstr a)      -- ^ \all x:t. p => c

cstr2dstr :: Cstr a -> Dstr a
cstr2dstr (Head p a) = DHead (pred2dred p) a
cstr2dstr (CAnd c) = DAnd (cstr2dstr <$> c)
cstr2dstr (All b c) = DAll (bind2dind b) (cstr2dstr c)
cstr2dstr (Any _ _) = error "Classic Eliminate doesn't support ebinds"

dstr2cstr :: Dstr a -> Cstr a
dstr2cstr (DHead p a) = Head (dred2pred p) a
dstr2cstr (DAnd c) = CAnd (dstr2cstr <$> c)
dstr2cstr (DAll b c) = All (dind2bind b) (dstr2cstr c)

pred2dred :: Pred -> Dred
pred2dred (Reft c) = DReft c
pred2dred (Var c1 c2) = DVar c1 c2
pred2dred (PAnd c) = DPAnd (pred2dred <$> c)

dred2pred :: Dred -> Pred
dred2pred (DReft p) = Reft p
dred2pred (DVar c1 c2) = Var c1 c2
dred2pred (DPAnd c) = PAnd (dred2pred <$> c)
dred2pred (DPOr c) = Reft $ F.POr $ dred2expr <$> c

dred2expr :: Dred -> F.Expr
dred2expr (DReft p) = p
dred2expr (DVar{}) = error "KVARS HAVEN'T BEEN ELIMINATED IN RHS OF ELIMINATE"
dred2expr (DPAnd c) = F.PAnd (dred2expr <$> c)
dred2expr (DPOr c) = F.POr (dred2expr <$> c)

bind2dind :: Bind -> Dind
bind2dind (Bind x t p) = Dind x t (pred2dred p)

dind2bind :: Dind -> Bind
dind2bind (Dind x t p) = Bind x t (dred2pred p)
