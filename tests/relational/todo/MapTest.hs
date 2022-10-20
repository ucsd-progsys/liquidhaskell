module MapTest where

import Prelude hiding (map)

data List a = Nil | Cons a (List a) deriving Eq

{-@ reflect lenList @-}
{-@ lenList :: List a -> Int @-}
lenList :: List a -> Int
lenList Nil = 0
lenList (Cons _ xs) = 1 + (lenList xs)

{-@ reflect diff @-}
{-@ diff :: xs:List Int -> ys:{List Int|lenList ys == lenList xs} -> Int @-}
diff :: List Int -> List Int -> Int
diff (Cons x xs) (Cons y ys)
  | x == y = diff xs ys
diff (Cons x xs) (Cons y ys)
  | x /= y = 1 + diff xs ys
diff _ _                        = 0

-- map :: (Int -> Int) -> List Int -> List Int
-- map _ Nil = Nil
-- map f (Cons x xs) = Cons (f x) (map f xs)
-- {-@ relational map ~ map ::
--                     f1:(x1:Int -> Int) -> xs1:List Int -> List Int ~
--                     f2:(x2:Int -> Int) -> xs2:List Int -> List Int 
--                      | xs1 = xs2 => true => true @-}

{-@ reflect diff' @-}
{-@ diff' :: xs:List Int -> ys:{List Int|lenList ys == lenList xs} -> Bool @-}
diff' :: List Int -> List Int -> Bool
diff' (Cons x xs) (Cons y ys)
  | x == y = True && diff' xs ys
diff' (Cons x xs) (Cons y ys)
  | x /= y = False && diff' xs ys
diff' _ _                        = True

map :: (Int -> Int) -> List Int -> List Int
map _ Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)
{- relational map ~ map ::
                    f1:(x1:Int -> Int) -> xs1:List Int -> List Int ~
                    f2:(x2:Int -> Int) -> xs2:List Int -> List Int 
                     | f1 = f2 => MapTest.lenList xs1 = MapTest.lenList xs2 => MapTest.diff' xs1 xs2 @-}
-- {-@ relational map ~ map :: f1:(x1:_ -> _) -> xs1:_ -> _ ~ f2:(x2:_ -> _) -> xs2:_ -> _ 
--                          | f1 == f2 => true => Fixme.diff xs1 xs2 >= Fixme.diff (r1 f1 xs1) (r2 f2 xs2) @-}

