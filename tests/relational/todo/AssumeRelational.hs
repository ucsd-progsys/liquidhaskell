module AssumeRelational where

update :: Int -> Int -> Int
update _ _ = 0

updates :: [Int] -> Int -> Int
updates []       w = w
updates (z : zs) w = updates zs (update z w)

{-@ reflect diff @-}
{-@ diff :: xs:[Int] -> ys:{[Int]|len ys == len xs} -> Int @-}
diff :: [Int] -> [Int] -> Int
diff (x : xs) (y : ys) | x == y = diff xs ys
diff (x : xs) (y : ys) | x /= y = 1 + diff xs ys
diff _ _                        = 0

{-@ assume relational update ~ update :: z1:Int -> w1:Int -> Int ~ z2:Int -> w2:Int -> Int 
                               | z1 = z2 => true => r1 z1 w1 - r2 z2 w2 = w1 - w2 @-}

{-@ assume relational update ~ update :: z1:Int -> w1:Int -> Int ~ z2:Int -> w2:Int -> Int 
                               | true => true => r1 z1 w1 - r2 z2 w2 <= w1 - w2 + 5 @-}

{-@ relational updates ~ updates :: zs1:[Int] -> w1:Int -> Int ~ zs2:[Int] -> w2:Int -> Int
                                 | len zs1 = len zs2 => true => 
                                        r1 zs1 w1 - r2 zs2 w2 <= w1 - w2 + 5 * AssumeRelational.diff zs1 zs2 @-}