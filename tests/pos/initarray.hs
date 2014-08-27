{-@ LIQUID "--no-termination" @-}

module Array () where

import Language.Haskell.Liquid.Prelude
import LiquidArray

{-@ zero ::
      i: {v: Int | v >= 0} ->
      n: Int ->
      a: (j: {v: Int | (0 <= v && v < i)} -> {v: Int | v = 0}) ->
      (k: {v: Int | (0 <= v && v < n)} -> {v: Int | v = 0}) @-}
zero :: Int -> Int -> (Int -> Int) -> (Int -> Int)
zero i n a = if i >= n then a
                       else zero (i + 1) n (set i 0 a)

{-@ tenZeroes :: i: {v: Int | (0 <= v && v < 10)} -> {v: Int | v = 0} @-}
tenZeroes = zero 0 10 empty

{-@ zeroBackwards ::
      i: Int ->
      n: {v: Int | v > i} ->
      a: (j: {v: Int | (i < v && v < n)} -> {v: Int | v = 0}) ->
      (k: {v: Int | (0 <= v && v < n)} -> {v: Int | v = 0}) @-}
zeroBackwards :: Int -> Int -> (Int -> Int) -> (Int -> Int)
zeroBackwards i n a = if i < 0 then a
                               else zeroBackwards (i - 1) n (set i 0 a)

{-@ tenZeroes' :: i: {v: Int | (0 <= v && v < 10)} -> {v: Int | v = 0} @-}
tenZeroes' = zeroBackwards 9 10 empty

{-@ zeroEveryOther ::
      i: {v: Int | (v >= 0 && v mod 2 = 0)} ->
      n: Int ->
      a: (j: {v: Int | (0 <= v && v < i && v mod 2 = 0)} -> {v: Int | v = 0}) ->
      (k: {v: Int | (0 <= v && v < n && v mod 2 = 0)} -> {v: Int | v = 0}) @-}
zeroEveryOther :: Int -> Int -> (Int -> Int) -> (Int -> Int)
zeroEveryOther i n a = if i >= n then a
                       else zeroEveryOther (i + 2) n (set i 0 a)

{-@ stridedZeroes ::
      j: {v: Int | (v mod 2 = 0 && 0 <= v && v < 10)} -> {v: Int | v = 0} @-}
stridedZeroes = zeroEveryOther 0 10 empty

{-@ initArray :: forall a <p :: x0: Int -> x1: a -> Prop>.
      f: (z: Int -> a<p z>) ->
      i: {v: Int | v >= 0} ->
      n: Int ->
      a: (j: {v: Int | (0 <= v && v < i)} -> a<p j>) ->
      (k: {v: Int | (0 <= v && v < n)} -> a<p k>) @-}
initArray f i n a = if i >= n then a
                              else initArray f (i + 1) n (set i (f i) a)

{-@ zeroInitArray ::
      i: {v: Int | v >= 0} ->
      n: Int ->
      a: (j: {v: Int | (0 <= v && v < i)} -> {v: Int | v = 0}) ->
      (k: {v: Int | (0 <= v && v < n)} -> {v: Int | v = 0}) @-}
zeroInitArray :: Int -> Int -> (Int -> Int) -> (Int -> Int)
zeroInitArray = initArray (const 0)

{-@ tenZeroes'' :: i: {v: Int | (0 <= v && v < 10)} -> {v: Int | v = 0} @-}
tenZeroes'' = zeroInitArray 0 10 empty

{-@ initid ::
      i: {v: Int | v >= 0} ->
      n: Int ->
      a: (j: {v: Int | (0 <= v && v < i)} -> {v: Int | v = j}) ->
      (k: {v: Int | (0 <= v && v < n)} -> {v: Int | v = k}) @-}
initid :: Int -> Int -> (Int -> Int) -> (Int -> Int)
initid = initArray id
