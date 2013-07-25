{--! run liquid with no-termination -}

module Intro where

import Language.Haskell.Liquid.Prelude  (liquidAssert)



{-@ zero' :: {v: Int | 0 <= v} @-}
zero' :: Int
zero' = 0


{-@ zero'' :: {v: Int | ((0 <= v) && (v < 100)) } @-}
zero'' :: Int
zero'' = 0


{-@ zero''' :: {v: Int | ((v mod 2) = 0) } @-}
zero''' :: Int
zero''' = 0


-- | A singleton type that precisely describes the constant

{-@ zero'''' :: {v: Int | v = 0 } @-}
zero'''' :: Int
zero'''' = 0


-- | A type that captures all the properties above:

{-@ zero :: {v: Int | ((0 <= v) && ((v mod 2) = 0)) } @-}
zero     :: Int
zero     =  0

-- | First, we can write a wrapper around the usual `error` function

{-@ error' :: {v: String | false } -> a  @-}
error'     :: String -> a
error'     = error


-- | Refinements encode arbitrary **assertions** via a function

{-@ lAssert     :: {v:Bool | (? (Prop v))} -> a -> a  @-}
lAssert         :: Bool -> a -> a
lAssert True  x = x
lAssert False _ = error' "lAssert failure"


-- | A *divide* function that *only accepts* non-zero denominators

{-@ divide :: Int -> {v: Int | v != 0 } -> Int @-}
divide     :: Int -> Int -> Int
divide n 0 = error' "divide by zero"
divide n d = n `div` d

-- | If you are paranoid, you can put in an explicit assertion

{-@ divide' :: Int -> {v: Int | v != 0 } -> Int @-}
divide'     :: Int -> Int -> Int
divide' n 0 = error' "divide by zero"
divide' n d = lAssert (d /= 0) $ n `div` d



-- | The following simple *absolute value* function has an output
-- refinement that specifies that the function returns non-negative values

{-@ abz :: Int -> {v: Int | 0 <= v } @-}
abz               :: Int -> Int
abz n | 0 < n     = n
      | otherwise = 0 - n


-- | `truncate i n` simply returns `i` if its absolute value is less the
-- upper bound `max`, and otherwise, *truncates* the value at the maximum.

{-@ truncate :: Int -> Int -> Int @-}
truncate i max
  | i' <= max' = i
  | otherwise  = max' * (i `divide` i')
    where i'   = abz i
          max' = abz max


{-@ truncate' :: Int -> Int -> Int @-}
truncate' i max
  | i' <= max' = i
  | otherwise  = lAssert (i' /= 0) $ max' * (i `divide` i')
    where i'   = abz i
          max' = abz max


{-@ truncate'' :: Int -> Int -> Int @-}
truncate'' i max
  | i' <= max' = i
  | otherwise  = liquidAssert (i' /= 0) $ max' * (i `divide` i')
    where i'   = abz i
          max' = abz max



