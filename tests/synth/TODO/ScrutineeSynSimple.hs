{-@ LIQUID "--typed-holes" @-}

module ScrutineeSynSimple where

import qualified Data.Set as S

import Language.Haskell.Liquid.Synthesize.Error

{-@ inline abs' @-}
{-@ abs' :: Int -> Nat @-}
abs' :: Int -> Int 
abs' x = if x >= 0 then x else -x

{-@ split :: xs: [a] -> 
    { v: ( { v: [a] | abs' (len xs - 2 * len v) <= 1 }, [a])
                      | len xs == len (fst v) + len (snd v) &&
                        listElts xs == S.union (listElts (fst v)) (listElts (snd v)) }
 @-}
split :: [a] -> ([a], [a])
split xs = 
    case xs of 
        [] -> (xs, xs)
        x5:x6 -> 
            case x6 of
                [] -> (x6, xs)
                x11:x12 ->
                    case split x12 of
                        (x16, x17) -> (x11:x16, x5:x17)


{-@ caseSplit1 :: xs: [a] -> { v: [a] | abs' (2 * len v - len xs) <= 1 } @-}
caseSplit1 :: [a] -> [a]
caseSplit1 = _goal
-- caseSplit1 xs = 
--     case split xs of 
--         (x1, x2) -> x1
