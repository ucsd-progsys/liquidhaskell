module Fixme where

import           Prelude                 hiding ( map )

import GHC.Types

{-@ reflect diff @-}
{-@ diff :: xs:[Int] -> ys:{[Int]|len ys == len xs} -> Int @-}
diff :: [Int] -> [Int] -> Int
diff (x : xs) (y : ys) | x == y = diff xs ys
diff (x : xs) (y : ys) | x /= y = 1 + diff xs ys
diff _ _                        = 0

{-@ reflect map @-}
map :: (Int -> Int) -> [Int] -> [Int]
map _ []       = []
map f (x : xs) = f x : map f xs

{-@ relational map ~ map :: { f1:(x1:_ -> _) -> xs1:_ -> _ 
                            ~ f2:(x2:_ -> _) -> xs2:_ -> _ 
                            | true :=> len xs1 = len xs2 :=> len (r1 f1 xs1) = len (r2 f2 xs2)} @-}

