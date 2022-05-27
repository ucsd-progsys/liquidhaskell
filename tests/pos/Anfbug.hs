{-@ LIQUID "--no-termination" @-}

module Anfbug (x,y) where

import Control.Exception (assert)

-- TransformRec BUG: this causes a temporary to get hoisted out of scope
getTails' :: Int -> [[a]] -> [[a]]
getTails' n xss = assert (n > 0) [t | (_:t) <- xss]

x = getTails' 1 []

-- HACK give hints for internal variables....
{- decrease ds_d258 3 @-}
{- decrease ds_d25g 3 @-}

-- TransformRec BUG: this causes some weird unused variable error (occurrence of DEAD ID)?
getTails'' :: Int -> [[a]] -> [[a]]
getTails'' n xss = [t | (_:t) <- xss]

y = getTails'' 1 []
