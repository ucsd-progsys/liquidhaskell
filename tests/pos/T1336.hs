module T1336 where

import Data.Ratio 

{-@ embed Ratio * as int @-}

-- | You can also write: 
--
--     embed Ratio * as real 
--
--   if for some reason you need to treat the values thus.

{-@ foo :: {v:Ratio Int | v /= 0} -> Bool @-}
foo :: Ratio Int -> Bool
foo x = y == y 
  where 
    y = 10 / x
