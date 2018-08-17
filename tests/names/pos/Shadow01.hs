-- TAG: resolve 
-- this tests whether we can resolve the name 'map' to the local binder, not 'GHC.Base.map'.

module Shadow01 where

{-@ incr :: map:Int -> {v:Int | v = map + 1} @-}
incr :: Int -> Int 
incr x = x + 1 
