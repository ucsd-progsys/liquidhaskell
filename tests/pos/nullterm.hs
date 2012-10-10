module NullTerm where

import Language.Haskell.Liquid.Prelude

-- Note how predicate polymorphism is used to abstract over the array's
-- bounds in both set and get.
{-@ set :: forall a <p :: x0: Int -> x1: a -> Bool, r :: x0: Int -> Bool>.
      i: Int<r> ->
      x: a<p i> ->
      a: (j: {v: Int<r> | v != i} -> a<p j>) ->
      (k: Int<r> -> a<p k>) @-}
set :: Int -> a -> (Int -> a) -> (Int -> a)
set i x a = \k -> if k == i then x else a k

{-@ get :: forall a <p :: x0: Int -> x1: a -> Bool, r :: x0: Int -> Bool>.
             i: Int<r> ->
             a: (j: Int<r> -> a<p j>) ->
             a<p i> @-}
get :: Int -> (Int -> a) -> a
get i a = a i

upperCaseString' :: Int -> Int -> (Int -> Int) -> (Int -> Int)
upperCaseString' n i s =
  let c = get i s in
  if c == 0 then s
            else upperCaseString' n (i + 1) (set i (c + 32) s)

{-@ upperCaseString ::
      n: {v: Int | v > 0} ->
      s: (j: {v : Int | (0 <= v && v < n)} ->
          {v: Int | (j = n - 1 => v = 0)}) ->
      (j: {v : Int | (0 <= v && v < n)} ->
       {v: Int | (j = n - 1 => v = 0)})
@-}
upperCaseString :: Int -> (Int -> Int) -> (Int -> Int)
upperCaseString n s = upperCaseString' n 0 s
