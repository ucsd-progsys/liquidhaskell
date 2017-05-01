module Client521 where

import Lib521 

{-@ bar :: { xs : [a] | size xs > 1 } -> [a] @-}
bar :: [a] -> [a]
bar xs = xs 
