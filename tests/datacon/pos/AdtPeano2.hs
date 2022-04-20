-- TAG: adt

{-@ LIQUID "--reflection" @-}

module AdtPeano2 where

data Influx = Silly { goo :: Int }

{-@ test:: n:Int -> m:Int -> { v:() | Silly n == Silly m } -> { n == m } @-}
test :: Int -> Int -> () -> ()
test n m z = ()
