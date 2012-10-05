module Array where

import Language.Haskell.Liquid.Prelude

{-@ set :: forall a <p :: x0: Int -> x1: a -> Bool>.
             i: Int ->
             x: a<p i> ->
             a: (j: {v: Int | v != i} -> a<p j>) ->
             (k: Int -> a<p k>) @-}
set :: Int -> a -> (Int -> a) -> (Int -> a)
set i x a = \k -> if k == i then x else a k

{-@ get :: forall a <p :: x0: Int -> x1: a -> Bool>.
             i: Int ->
             (j: Int -> a<p j>) ->
             a<p i> @-}
get :: Int -> (Int -> a) -> a
get i a = a i

{-@ zero :: i: Int ->
            n: Int ->
            a: (j: Int ->
                {v: Int | (((0 <= j) && (j < i)) => ((v = 0)))}) ->
            (k: Int -> {v: Int | (((0 <= k) && (k < n)) => ((v = 0)))}) @-}
zero :: Int -> Int -> (Int -> Int) -> (Int -> Int)
zero i n a = if i >= n then a
                       else zero (i + 1) n (set i 0 a)

create x = \i -> x

{-@ tenZeroes :: j: Int -> {v: Int | (((0 <= j) && (j < 10)) => ((v = 0)))} @-}
tenZeroes = zero 0 10 (create 1)

-- TODO:
--  Backward initialization
--  Every other element initialization
--  Higher-order initialization