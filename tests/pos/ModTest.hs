module ModTest () where

import Language.Haskell.Liquid.Prelude (isEven)

{-@ type NZero = {v: Int | v /= 0} @-}

{-@ takeEvens :: [NZero] -> [{v: NZero | v mod 2 = 0}] @-}
takeEvens :: [Int] -> [Int]
takeEvens []     = []
takeEvens (x:xs) = if isEven x
                     then x : takeEvens xs 
                     else takeEvens xs 
