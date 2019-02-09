module Language.Fixpoint.Horn.Transformations (
  poke,
  elim,
  uniq
) where

import           Language.Fixpoint.Horn.Types
import qualified Language.Fixpoint.Types      as F
import qualified Data.HashMap.Strict          as M
import           Control.Monad (void)
import           Data.String                  (IsString (..))
import qualified Data.Set                     as S
import           Control.Monad.State
-- import           Language.Fixpoint.Misc (traceShow)

-- $setup
-- >>> :l src/Language/Fixpoint/Horn/Transformations.hs src/Language/Fixpoint/Horn/Parse.hs
-- >>> :m + *Language.Fixpoint.Horn.Parse
-- >>> import Language.Fixpoint.Parse
-- >>> :set -XOverloadedStrings

-- |
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
-- | uniq makes sure each binder has a uniqe name
------------------------------------------------------------------------------
type RenameMap = M.HashMap F.Symbol Integer

uniq :: Cstr a -> Cstr a
uniq c = evalState (uniq' c) M.empty

uniq' :: Cstr a -> State RenameMap (Cstr a)
uniq' (Head c a) = Head <$> gets (rename c) <*> pure a
uniq' (CAnd c) = CAnd <$> mapM uniq' c
uniq' (All b c2) = do
    b' <- uBind b
    All b' <$> uniq' c2
uniq' (Any b c2) = do
    b' <- uBind b
    Any b' <$> uniq' c2

uBind :: Bind -> State RenameMap Bind
uBind (Bind x t p) = do
   x' <- uVariable x
   Bind x' t <$> gets (rename p)

uVariable :: IsString a => F.Symbol -> State RenameMap a
uVariable x = do
   i <- gets (M.lookupDefault 0 x)
   modify (M.insert x (i+1))
   pure $ numSym x (i+1)

rename :: Pred -> RenameMap -> Pred
rename e m = substPred (M.mapWithKey numSym m) e

numSym :: IsString a => F.Symbol -> Integer -> a
numSym s i = fromString $ F.symbolString s ++ "#" ++ show i

substPred :: M.HashMap F.Symbol F.Symbol -> Pred -> Pred
substPred su (Reft e) = Reft $ F.subst (F.Su $ F.EVar <$> su) e
substPred su (PAnd ps) = PAnd $ substPred su <$> ps
substPred su (Var k xs) = Var k $ upd <$> xs
  where upd x = M.lookupDefault x x su


------------------------------------------------------------------------------
-- | elim solves all of the KVars in a Cstr (assuming no cycles...)
-- >>> elim . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test00.smt2"
-- (and (forall ((x int) (x > 0)) (forall ((y int) (y > x)) (forall ((v int) (v == x + y)) ((v > 0))))))
-- >>> elim . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test01.smt2"
-- (and (forall ((x int) (x > 0)) (and (forall ((y int) (y > x)) (forall ((v int) (v == x + y)) ((v > 0)))) (forall ((z int) (z > 100)) (forall ((v int) (v == x + z)) ((v > 100)))))))
-- >>> elim . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test02.smt2"
-- (and (forall ((x int) (x > 0)) (and (forall ((y int) (y > x + 100)) (forall ((v int) (v == x + y)) ((true)))) (forall ((y int) (y > x + 100)) (forall ((v int) (v == x + y)) (forall ((z int) (z == v)) (forall ((v int) (v == x + z)) ((v > 100)))))))))
------------------------------------------------------------------------------
elim :: Cstr a -> Cstr a
------------------------------------------------------------------------------
elim c = if S.null $ boundKvars res then res else error "called elim on cyclic fucker"
  where
  res = S.foldl elim1 c (boundKvars c)

elim1 :: Cstr a -> F.Symbol -> Cstr a
-- Find a `sol1` solution to a kvar `k`, and then subsitute in the solution for
-- each rhs occurence of k.
elim1 c k = doelim k sol c
  where sol = sol1 k (scope k c)

-- scope drops extraneous leading binders so that we can take the strongest
-- scoped solution instead of the strongest solution
scope :: F.Symbol -> Cstr a -> Cstr a
scope k = go . snd . scope' k
  where go (All _ c') = go c'
        go c = c

-- |
-- >>> sc <- scope' "k0" . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test02.smt2"
-- >>> sc
-- (True,(forall ((x ... (and (forall ((y ... (forall ((v ... ((k0 v)))) (forall ((z ...

-- scope' prunes out branches that don't have k
scope' :: F.Symbol -> Cstr a -> (Bool, Cstr a)

scope' k (CAnd c) = case map snd $ filter fst $ map (scope' k) c of
                     []  -> (False, CAnd [])
                     [c] -> (True, c)
                     cs  -> (True, CAnd cs)

-- TODO: Bind PAnd Case
scope' k c@(All (Bind x t (Var k' su)) c')
  | k == k' = (True, c)
  | otherwise = All (Bind x t (Var k' su)) <$> scope' k c'
scope' k c@(All _ c')
  = const c <$> scope' k c'
scope' _ (Any _ _) = error "ebinds don't work with old elim"

scope' k c@(Head (Var k' _) _)
-- this case seems extraneous?
  | k == k'   = (True, c)
scope' _ c@Head{} = (False, c)

-- | A solution is a Hyp of binders (including one anonymous binder
-- that I've singled out here).
-- (What does Hyp stand for? Hypercube? but the dims don't line up...)
--
-- >>> c <- qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test02.smt2"
-- >>> sol1 ("k0") (scope "k0" c)
-- [[((y int) (y > x + 100)),((v int) (v == x + y)),((_ bool) (κarg$k0#1 == v))]]
-- >>> c <- qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test03.smt2"
-- >>> sol1 ("k0") (scope "k0" c)
-- [[((x int) (x > 0)),((v int) (v == x)),((_ bool) (κarg$k0#1 == v))],[((y int) (k0 y)),((v int) (v == y + 1)),((_ bool) (κarg$k0#1 == v))]]

-- Naming conventions:
--  - `b` is a binder `forall . x:t .p =>`
--  - `bs` is a list of binders, or a "cube" that tracks all of the
--     information on the rhs of a given constraint
--  - `bss` is a Hyp, that tells us the solution to a Var, that is,
--     a collection of cubes that we'll want to disjunct

sol1 :: F.Symbol -> Cstr a -> [[Bind]]
sol1 k (CAnd cs) = sol1 k =<< cs
sol1 k (All b c) = (b:) <$> sol1 k c
sol1 k (Head (Var k' ys) _) | k == k'
  = [[Bind (fromString "_") F.boolSort $ Reft $ F.PAnd $ zipWith (F.PAtom F.Eq) (F.EVar <$> xs) (F.EVar <$> ys)]]
  where xs = zipWith const (kargs k) ys
sol1 _ (Head _ _) = []
sol1 _ (Any _ _) =  error "ebinds don't work with old elim"

kargs k = fromString . (("κarg$" ++ F.symbolString k ++ "#") ++) . show <$> [1..]

-- |
-- >>> let c = doParse' hCstrP "" "(forall ((z Int) ($k0 z)) ((z = x)))"
-- >>> doelim "k0" [[Bind "v" F.boolSort (Reft $ F.EVar "v"), Bind "_" F.boolSort (Reft $ F.EVar "donkey")]]  c
-- (forall ((v bool) (v)) (forall ((z int) (donkey)) ((z == x))))

doelim :: F.Symbol -> [[Bind]] -> Cstr a -> Cstr a
doelim k bp (CAnd cs)
  = CAnd $ doelim k bp <$> cs
doelim k bss (All (Bind x t (Var k' xs)) c)
  | k == k'
  -- quadratic blowup in number of constraints, uh oh!
  = mkAnd $ cubeSol . reverse <$> bss
  where su = F.Su $ M.fromList $ zip (kargs k) (F.EVar <$> xs)
        mkAnd [c] = c
        mkAnd cs = CAnd cs
        cubeSol ((Bind _ _ (Reft eqs)):xs) = foldl (flip All) (All (Bind x t (Reft $ F.subst su eqs)) $ doelim k bss c) xs
        cubeSol _ = error "internal error"
doelim k bp (All b c)
  = All b (doelim k bp c)
doelim k _ (Head (Var k' _) a)
  | k == k'
  = Head (Reft F.PTrue) a
doelim _ _ (Head p a) = Head p a
doelim _ _ (Any _ _) =  error "ebinds don't work with old elim"

-- | Returns a list of KVars with thier arguments that are present as
--
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/ebind01.smt2"
-- ... []
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/ebind02.smt2"
-- ... ["k"]
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test00.smt2"
-- ... []
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test01.smt2"
-- ... []
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test02.smt2"
-- ... ["k0"]
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test03.smt2"
-- ... ["k0"]

--- TODO, what about PAnd?
boundKvars :: Cstr a -> S.Set F.Symbol
boundKvars (Head (Var k _) _) = S.singleton k
boundKvars (Head _ _) = S.empty
boundKvars (CAnd c) = mconcat $ boundKvars <$> c
boundKvars (All (Bind _ _ (Var k _xs)) c) = S.insert k $ boundKvars c
boundKvars (All _ c) = boundKvars c
boundKvars (Any (Bind _ _ (Var k _xs)) c) = S.insert k $ boundKvars c
boundKvars (Any _ c) = boundKvars c
