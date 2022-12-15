module IncrVeryHO where

{-@ reflect incr @-}
incr :: Int -> Int
incr = (+ 1)

{-@ reflect incr' @-}
incr' :: (Int -> Int) -> Int -> Int
incr' incr x = incr x

{-@ relational incr' ~ incr' :: { g1:(z1:Int -> Int) -> x1:Int -> Int 
                                ~ g2:(z2:Int -> Int) -> x2:Int -> Int
                                | !(z1 < z2 :=> r1 < r2) :=> x1 < x2 :=> r1 g1 x1 < r2 g2 x2 } @-}

{-@ reflect incr'' @-}
incr'' :: ((Int -> Int) -> Int -> Int) -> Int -> Int
incr'' incr' x = incr' incr x

{-@ relational incr'' ~ incr'' :: { g1:((z1:Int -> Int) -> y1:Int -> Int) -> x1:Int -> Int
                                  ~ g2:((z2:Int -> Int) -> y2:Int -> Int) -> x2:Int -> Int
                                  | !(!(z1 < z2 :=> r1 < r2) :=> y1 < y2 :=> r1 < r2) 
                                        :=> x1 < x2 
                                        :=> r1 g1 x1 < r2 g2 x2 } @-}

{-@ reflect incr''' @-}
incr''' :: (Int -> Int) -> (Int -> Int) -> Int -> Int
incr''' incr1 incr2 x = incr1 (incr2 x)

{-@ relational incr''' ~ incr''' :: { f1:(y1:Int -> Int) -> g1:(z1:Int -> Int) -> x1:Int -> Int 
                                    ~ f2:(y2:Int -> Int) -> g2:(z2:Int -> Int) -> x2:Int -> Int
                                    | !(y1 < y2 :=> r1 < r2) 
                                        :=> !(z1 < z2 :=> r1 < r2) 
                                        :=> x1 < x2 
                                        :=> r1 g1 x1 < r2 g2 x2 } @-}

{-@ reflect incr'''' @-}
incr'''' :: Int -> (Int -> Int) -> Int
incr'''' x incr = incr x

{-@ relational incr'''' ~ incr'''' :: { x1:Int -> g1:(z1:Int -> Int) -> Int 
                                      ~ x2:Int -> g2:(z2:Int -> Int) -> Int
                                      | x1 < x2 :=> !(z1 < z2 :=> r1 < r2) :=> r1 g1 x1 < r2 g2 x2 } @-}
