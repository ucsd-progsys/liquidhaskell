{-@ LIQUID "--totality" @-}
{-# LANGUAGE EmptyDataDecls #-}

module PropMeasure where

import Prelude hiding (length)

{-@ myhead :: {v:[a] | nonEmpty v} -> a @-}
myhead (x:_) = x

{-@ measure nonEmpty @-}   
nonEmpty (x:xs) = True 
nonEmpty []     = False

{-@ measure length @-}   
length :: [a] -> Int
length (x:xs) = 1 + length xs 
length []     = 0


{-@ measure lenEqFive @-}   
lenEqFive (x:xs) = length xs == 4
lenEqFive []     = False

{-@ measure lenNEqFive @-}   
lenNEqFive (x:xs) = not (length xs == 4)
lenNEqFive []     = True


{-@ measure lenGEFour @-}   
lenGEFour (x:xs) = length xs >= 3
lenGEFour []     = False


{-@ len3 :: {v:[Int] | (not (lenEqFive v))} @-}
len3 :: [Int]
len3 = [1, 2, 3]


{-@ len5 :: {v:[Int] | (lenEqFive v) && (lenGEFour v) } @-}
len5 :: [Int]
len5 = [1, 2, 3, 4, 5]

{-@ measure length @-}

{-@ foo  :: x:[a] -> {v: Bool | (Prop v) <=> (nonEmpty x) } @-}
foo  :: [a] -> Bool
foo x = nonEmpty x


cons = (:)
nil  = []








