module WrapClient where

import WrapLib
import WrapLibCode 

{-@ bar :: {v:Int | v = 2 } @-}
bar = foo 1

