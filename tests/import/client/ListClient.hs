-- | A "client" that uses the reflected definitions.

{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-} 

module ListClient where

import Prelude hiding (concat, filter, foldr, map)
import ListLib

{-@ reflect incr @-}
incr :: Int -> Int
incr x = x + 1

{-@ reflect isPos @-}
isPos :: Int -> Bool 
isPos x = x > 0 

{-@ reflect ints0 @-}
ints0 :: [Int] 
ints0 = [0, 1, 2] 

{-@ reflect ints1 @-}
ints1 :: [Int] 
ints1 = [1, 2, 3] 

{-@ reflect ints2 @-}
ints2 :: [Int] 
ints2 = [1, 2] 

{-@ mapProp :: () -> { map incr ints0 == ints1 } @-}
mapProp () = ()

{-@ filterProp :: () -> { filter isPos ints0 == ints2 } @-}
filterProp () = ()


