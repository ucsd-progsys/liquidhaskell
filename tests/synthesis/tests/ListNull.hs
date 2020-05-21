{-@ LIQUID "--typed-holes" @-}

module ListNull where

import Language.Haskell.Liquid.Synthesize.Error

{-@ true :: { v: Bool | v } @-}
true :: Bool
true = True

{-@ false :: {v: Bool | not v} @-}
false :: Bool
false = False

{-@ isNull :: xs: [a] -> { v: Bool | (len xs == 0) <=> v } @-}
isNull :: [a] -> Bool
isNull = _goal
-- isNull [] = true
-- isNull _  = false
