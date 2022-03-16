{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell -Wno-incomplete-patterns #-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--ple" @-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.Data.List
-- Copyright   :  (C) 2021 Facundo Domínguez
-- License     :  BSD-style (see LICENSE)
-- Stability   :  experimental
--
-- An interface of lists that can be used in reflected definitions
-- with LH
--
----------------------------------------------------------------------------

module Language.Stitch.LH.Data.List where

import Language.Haskell.Liquid.ProofCombinators ((?), trivial, Proof)
import Language.Stitch.LH.Data.Nat
import Prelude hiding (head, length, map, tail, take)


-- XXX: Using a custom List instead of [a] avoids LH error: unknown function/constant smt_set_sng
data List a = Cons { head :: a, tail :: List a } | Nil

{-@
inline empty
empty :: { xs : List a | length xs = 0 }
@-}
empty :: List a
empty = Nil

{-@
inline cons
cons :: a -> xs : List a -> { ys : List a | length ys = 1 + length xs }
@-}
cons :: a -> List a -> List a
cons a b = Cons a b

{-@
reflect elemAt
elemAt :: n : Nat -> { xs : List a | length xs > n } -> a
@-}
elemAt :: Nat -> List a -> a
elemAt 0 (Cons x _) = x
elemAt i (Cons _ xs) = elemAt (i-1) xs

{-@
reflect take
take
  :: n : Nat
  -> { xs : List a | length xs >= n }
  -> { ys : List a | length ys = n}
@-}
take :: Nat -> List a -> List a
take 0 _ = Nil
take i (Cons x xs) = Cons x (take (i-1) xs)

{-@
measure length
length :: xs : List a -> Nat
@-}
length :: List a -> Nat
length Nil = 0
length (Cons _ xs) = 1 + length xs

{-@
reflect append
append ::
  xs : List a ->
  ys : List a ->
  { zs : List a | length zs == length xs + length ys }
 @-}
append :: List a -> List a -> List a
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

{-@
appendLengh
  :: xs : List a
  -> ys : List a
  -> { length (append xs ys) == length xs + length ys}
@-}
appendLengh :: List a -> List a -> Proof
appendLengh xs ys = trivial ? append xs ys

{-@
elemAtThroughAppend
  :: i : Nat
  -> xs : { xs : List a | i < length xs }
  -> ys : List a
  -> { elemAt i (append xs ys) = elemAt i xs }
@-}
elemAtThroughAppend :: Nat -> List a -> List a -> Proof
elemAtThroughAppend i xs ys =
  if i == 0 then trivial
  else case xs of
    Cons _ xss -> elemAtThroughAppend (i - 1) xss ys
    Nil -> trivial
