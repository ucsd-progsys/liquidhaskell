{-@ measure d :: a -> a -> Double @-}
{-@ assume d :: x:a -> y:a -> {v:Double | v = d x y } @-}
d :: a -> a -> Double
d x y = undefined

{-@ reflect diff @-}
{-@ diff :: xs:[Int] -> ys:{[Int]|len ys == len xs} -> Int @-}
diff :: [Int] -> [Int] -> Int
diff (x : xs) (y : ys) | x == y = diff xs ys
diff (x : xs) (y : ys) | x /= y = 1 + diff xs ys
diff _ _                        = 0

filter' :: Double -> (Int -> Bool) -> [Int] -> [Int]
filter' _ _ [] = []
filter' k pred (el:els) | pred el   = el:filter' k pred els
                        | otherwise =    filter' k pred els
{-@ relational filter' ~ filter' ::
                        k1:Double -> f1:(x1:Int -> Bool) -> xs1:[Int] -> [Int] ~
                        k2:Double -> f2:(x2:Int -> Bool) -> xs2:[Int] -> [Int]
                         ~~ k1 = k2 => (true => d x1 x2 <= k1) => len xs1 = len xs2
                            => d(r1 f1 xs1, r2 f2 xs2)
                                     <= diff xs1 xs2 * k1 @-}



add :: Int -> Int -> Int
add x y = x + y
{-@ relational add ~ add :: x1:Int -> y1:Int -> Int ~
                            x2:Int -> y2:Int -> Int
                         ~~ x1 == x2 => y1 == y2 =>
                            r1 x1 y1 == r2 x2 y2 @-}

abs :: Int -> Int
abs x = if x < 0 then -x else x

{-@ relational abs ~ abs :: x1:Int -> Int ~
                            x2:Int -> Int
                         ~~ 0 <= x1 && x1 < x2 =>
                            r1 x1 < r2 x2 @-}
