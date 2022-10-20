module Filter where

{-@ measure d :: a -> a -> Double @-}
{-@ assume d :: x:a -> y:a -> {v:Double | v = d x y } @-}
d :: a -> a -> Double
d x y = undefined

-- Lam. fix filter(f). Lam. Lam. lam l. caseL l of 
--    nil => pack nil
--  | h::tl => let r' = filter f [] [] tl in
--    	    let b = (f h) in
--             unpack r' as r in if b then pack (h::r) else pack r
-- 
-- <= 0 : forall k.  ((B ((U int) [diff, k] -> U bool)) => forall i; alpha. 
--  (list[i,alpha] U int) [diff, k * alpha] -> U (exists j ::size.  (list[j] int)))
--
-- From: https://github.com/ezgicicek/BiRelCost/blob/master/examples/binary/filter.br

data List a = Nil | Cons a (List a)

{-@ reflect lenList @-}
{-@ lenList :: List a -> Int @-}
lenList :: List a -> Int
lenList Nil = 0
lenList (Cons _ xs) = 1 + lenList xs

-- {-@ reflect diff @-} {-@ diff :: xs:[Int] -> ys:{[Int]|len ys ==
-- len xs} -> Int @-} diff :: [Int] -> [Int] -> Int diff (x : xs) (y :
-- ys) | x == y = diff xs ys diff (x : xs) (y : ys) | x /= y = 1 +
-- diff xs ys diff _ _ = 0

{-@ reflect diff @-}
{-@ diff :: xs:List Int -> ys:{List Int|lenList ys == lenList xs} -> Int @-}
diff :: List Int -> List Int -> Int
diff (Cons x xs) (Cons y ys)
  | x == y = diff xs ys
diff (Cons x xs) (Cons y ys)
  | x /= y = 1 + diff xs ys
diff _ _                        = 0

filter' :: Double -> (Int -> Bool) -> List Int -> List Int
filter' _ _ Nil = Nil
filter' k pred (Cons el els)
  | pred el   = Cons el (filter' k pred els)
  | otherwise = filter' k pred els
{-@ relational filter' ~ filter' ::
      k1:Double -> f1:(Int -> Bool) -> xs1:List Int -> List Int ~
      k2:Double -> f2:(Int -> Bool) -> xs2:List Int -> List Int
         | k1 = k2 => true => f1 = f2 && Filter.lenList xs1 = Filter.lenList xs2 => true @-}

{- relational filter' ~ filter' ::
                        k1:Double -> f1:(x1:Int -> Bool) -> xs1:List Int -> List Int ~
                        k2:Double -> f2:(x2:Int -> Bool) -> xs2:List Int -> List Int
                         | k1 = k2 => (true => d x1 x2 <= k1) => lenList xs1 = lenList xs2
                            => d (r1 f1 xs1) (r2 f2 xs2)
                                     <= diff xs1 xs2 * k1 @-}



add :: Int -> Int -> Int
add x y = x + y
{-@ relational add ~ add :: x1:Int -> y1:Int -> Int ~
                            x2:Int -> y2:Int -> Int
                         | x1 == x2 => y1 == y2 =>
                            r1 x1 y1 == r2 x2 y2 @-}

abs :: Int -> Int
abs x = if x < 0 then -x else x

{-@ relational abs ~ abs :: x1:Int -> Int ~
                            x2:Int -> Int
                         | 0 <= x1 && x1 < x2 =>
                            r1 x1 < r2 x2 @-}
