module T1336 where 

import Data.Ratio 

{-@ embed Ratio * as int @-}

{-@ foo :: {v:Ratio Int | v /= 0} -> Bool @-}
foo :: Ratio Int -> Bool
foo x = y == y 
  where 
    y = 10 / x
