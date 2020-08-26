{-@ LIQUID "--reflection" @-}

module T1738 where

import T1738Lib

{-@ reflect bar @-}
bar :: Int -> Int
bar n = incr n
