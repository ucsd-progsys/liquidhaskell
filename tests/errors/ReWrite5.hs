{-@ LIQUID "--expect-error-containing=parameter \"xs\" contains an inner refinement" @-}
module ReWrite5 where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ infix ++ @-}

import Prelude hiding (filter)

{-@ reflect lt5 @-}
lt5 :: Int -> Bool
lt5 x = x < 5

{-@ reflect filter @-}
filter _ []     = []
filter p (x:xs) = if p x then x:(filter p xs) else filter p xs

-- Reject inner refinements
{-@ rw :: xs :  [{ v: Int | v > 5 }] -> { filter lt5 xs = [] } @-}
rw :: [Int] -> ()
rw []     = ()
rw (_:xs) = rw xs

{-@ rewriteWith bad [rw] @-}
{-@ bad :: xs : [Int] -> { filter lt5 xs = [] } @-}
bad :: [Int] -> ()
bad _ = ()
