module PredAbs where

{-@ foo :: forall < p :: Int -> Bool
                  , q :: Int -> Bool >. Int<p,q> -> Int<p> @-}
foo :: Int -> Int
foo x = x

{-@ relational foo ~ foo :: { x1:Int -> Int 
                            ~ x2:Int -> Int
                            | x1 < x2 :=> r1 x1 < r2 x2 } @-}
