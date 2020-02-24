{-@ LIQUID "--typed-holes" @-}

module ListSplit where

import qualified Data.Set as S

import Language.Haskell.Liquid.Synthesize.Error

{-@ inline abs' @-}
{-@ abs' :: Int -> Nat @-}
abs' :: Int -> Int 
abs' x = if x >= 0 then x else -x

-- Case split on expressions 
{-@ split :: xs: [a] -> 
    { v: ( { v: [a] | abs' (len xs - 2 * len v) <= 1 }, [a])
                      | len xs == len (fst v) + len (snd v) &&
                        listElts xs == S.union (listElts (fst v)) (listElts (snd v)) }
 @-}
split :: [a] -> ([a], [a])
split = _goal
-- split xs = 
--     case xs of 
--         [] -> (xs, xs)
--         x5:x6 -> 
--             case x6 of
--                 [] -> (x6, xs)
--                 x11:x12 ->
--                     case split x12 of
--                         (x16, x17) -> (x11:x16, x5:x17)
