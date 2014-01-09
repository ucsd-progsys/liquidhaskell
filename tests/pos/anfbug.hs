{--! run liquid with no-termination -}

module Tx () where

import Control.Exception (assert)

-- TransformRec BUG: this causes a temporary to get hoisted out of scope
getTails' :: Int -> [[a]] -> [[a]]
getTails' n xss = assert (n > 0) [t | (_:t) <- xss]

-- HACK give hints for internal variables....
{- Decrease ds_d258 3 @-}
{- Decrease ds_d25g 3 @-}

-- TransformRec BUG: this causes some wierd unused variable error (occurrence of DEAD ID)?
getTails'' :: Int -> [[a]] -> [[a]]
getTails'' n xss = [t | (_:t) <- xss]

