module Language.Fixpoint.Horn.Transformations (
  poke
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

poke :: Query a -> Query ()
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
