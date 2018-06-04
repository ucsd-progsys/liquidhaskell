module RepeatAdd (main) where

{-@ rpt :: n:Int ~> m:Int ~> (z:Int ~> y:{z=m} -> v:{v=y+z}) -> k:_ -> x:{x=n} -> {v:_|v=(n+k*m)} @-}
rpt :: (Int -> Int) -> Int -> Int -> Int
rpt f k x = if k <= 0 then x else f (rpt f (k - 1) x)


{-@ main :: n:{n>=0} -> k:{k>0} -> v:{v>=n} @-}
main :: Int -> Int -> Int
main n k = rpt addn k 0
  where {-@ addn :: z:Int ~> y:Int -> v:{v = n+y} @-}
        addn :: Int -> Int
        addn = (+ n)
