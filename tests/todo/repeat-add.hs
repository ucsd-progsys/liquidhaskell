module RepeatAdd (main) where

{-@ rpt :: n:Int ~> m:Int ~> (y:{y=n} -> {v:Int|v=m}) -> k:_ -> x:{x=n} -> {v:_|v=(n+k*(m-n))} @-}
rpt :: (Int -> Int) -> Int -> Int -> Int
rpt f k x = if k <= 0 then x else f (rpt f (k - 1) x)

{-@ main :: n:{n>=0} -> k:{k>0} -> () @-}
main :: Int -> Int -> ()
main n k = assert (rpt (+ n) k 0 >= n)

{-@ assert :: {v:Bool | v} -> () @-}
assert :: Bool -> ()
assert x = ()
