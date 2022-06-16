{-@ LIQUID "--expect-any-error" @-}
module Inc04 where

import Inc04Lib 

-- Check that the alias and SIG for down are getting imported
{-@ test1 :: NN -> NN @-} 
test1 :: Int -> Int 
test1 x = down x 

