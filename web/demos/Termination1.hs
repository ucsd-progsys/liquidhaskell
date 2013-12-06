module Termination where

import Prelude     hiding (sum)
import Data.Vector hiding (sum)

-- | Looping Over Vectors

type Val  = Int
type Vec = Vector Val

{-@ sum :: a:Vec -> {v:Nat | v < (vlen a)} -> Val @-}
sum     :: Vec -> Int -> Val

sum a 0 = 0
sum a n = (a ! (n-1)) + sum a (n-1)


-- | Choosing the Correct Argument

{-@ Decrease sum' 3 @-}

{-@ sum' :: a:Vec -> Val -> {v:Nat| v < (vlen a)} -> Val @-}
sum' :: Vec -> Val -> Int -> Val

sum' a acc 0 = acc + a!0 
sum' a acc n = sum' a (acc + a!n) (n-1)

