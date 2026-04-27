{- | Regression test: when a lambda predicate has fewer arguments than
     the formal abstract predicate, arguments must bind left-to-right
     to the formal parameters (not shift to the value position).

     Here p :: a -> a -> b -> Bool has 3 args, but the lambda {\x y -> x >= y}
     has only 2. The correct binding is x→1st arg, y→2nd arg. With the data
     declaration p pfst pfst, the constraint becomes pfst >= pfst which is
     trivially true (SAFE).

     If arguments were shifted (old bug), y would bind to the value type
     (psnd), giving pfst >= psnd = 1 >= 2 = UNSAFE.
-}
module PartialPredArgs where

{-@ data Pair a b <p :: a -> a -> b -> Bool>
      = MkPair { pfst :: a, psnd :: b<p pfst pfst> } @-}
data Pair a b = MkPair { pfst :: a, psnd :: b }

{-@ foo :: Pair <{\x y -> x >= y}> Int Int @-}
foo :: Pair Int Int
foo = MkPair 1 2
