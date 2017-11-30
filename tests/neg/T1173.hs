module ORM where

{-@ LIQUID "--no-adt" 	      @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--ple"            @-}

import Prelude hiding (length, filter)

-- OK
{-@ prop1 :: [Int] -> [{v:Int | v == 100}] @-}
prop1 :: [Int] -> [Int]
prop1 = filterQQ (QQ 10)

-- FAILS
{-@ prop2 :: [Int] -> [{v:Int | v == 10}] @-}
prop2 :: [Int] -> [Int]
prop2 = filterQQ (mkQQ 10)

{-@ reflect mkQQ @-}
mkQQ :: Int -> QQ
mkQQ n = QQ n

{-@ filterQQ :: q:QQ -> [Int] -> [{v:Int | evalQQ q v}] @-}
filterQQ :: QQ -> [Int] -> [Int]
filterQQ q = filter (evalQQ q)


--------------------------------------------------------------------------------
-- | DB API
--------------------------------------------------------------------------------

data QQ  = QQ Int

{-@ reflect evalQQ @-}
evalQQ :: QQ -> Int -> Bool
evalQQ (QQ x) y = x == y

--------------------------------------------------------------------------------
-- | Generic List API
--------------------------------------------------------------------------------

{-@ filter :: f:(a -> Bool) -> [a] -> [{v:a | f v}] @-}
filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x         = x : filter f xs
  | otherwise   =     filter f xs
filter _ []     = []
