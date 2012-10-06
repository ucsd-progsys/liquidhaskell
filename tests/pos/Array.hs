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

{-@ zero ::
      i: Int ->
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

{-@ zeroBackwards ::
      i: Int ->
      n: Int ->
      a: (j: Int ->
          {v: Int | (((i < j) && (j < n)) => ((v = 0)))}) ->
      (k: Int -> {v: Int | (((0 <= k) && (k < n)) => ((v = 0)))}) @-}
zeroBackwards :: Int -> Int -> (Int -> Int) -> (Int -> Int)
zeroBackwards i n a = if i < 0 then a
                               else zeroBackwards (i - 1) n (set i 0 a)

{-@ tenZeroes :: j: Int -> {v: Int | (((0 <= j) && (j < 10)) => ((v = 0)))} @-}
tenZeroes' = zeroBackwards 9 10 (create 1)

{-@ zeroEveryOther ::
      i: {v : Int | v mod 2 = 0} ->
      n: Int ->
      a: (j: Int ->
          {v: Int | (((j mod 2 = 0) && (0 <= j) && (j < i)) => ((v = 0)))}) ->
      (k: Int -> {v: Int | (((k mod 2 = 0) && (0 <= k) && (k < n)) => ((v = 0)))}) @-}
zeroEveryOther :: Int -> Int -> (Int -> Int) -> (Int -> Int)
zeroEveryOther i n a = if i >= n then a
                       else zeroEveryOther (i + 2) n (set i 0 a)

{-@ stridedZeroes ::
      j: Int ->
      {v: Int | (((j mod 2 = 0) && (0 <= j) && (j < 10)) => ((v = 0)))} @-}
stridedZeroes = zeroEveryOther 0 10 (create 1)

-- TODO:
--  Higher-order initialization