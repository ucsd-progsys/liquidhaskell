{-@ LIQUID "--typed-holes" @-}

module BinHeapSingleton where

import qualified Data.Set as S
import Language.Haskell.Liquid.Synthesize.Error

{-@ data Heap [size] a = Empty | Node { x :: a, l :: Heap { v: a | v > x }, r :: Heap { v: a | v > x } } @-}
data Heap a = Empty | Node a (Heap a) (Heap a)

{-@ measure size @-}
{-@ size :: Heap a -> Nat @-}
size :: Heap a -> Int
size Empty        = 0
size (Node x l r) = 1 + size l + size r

{-@ measure heapElts @-}
{-@ heapElts :: Heap a -> S.Set a @-}
heapElts Empty        = S.empty
heapElts (Node x l r) = S.union (S.singleton x) (S.union (heapElts l) (heapElts r))

{-@ singleton :: x: a -> { v: Heap a | heapElts v == S.singleton x } @-}
singleton :: a -> Heap a
singleton = _goal
-- singleton x = Node x Empty Empty