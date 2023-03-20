{- 2DCount 16/3/24 | Changed on Nov 22 2022 -}
{-# LANGUAGE  FlexibleContexts #-}
{-@ LIQUID "--relational-hints" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module R2Dcounting
  ( module R2Dcounting ) where

{-@ infix <*> @-}
{-@ infix :   @-}

import RTick
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (return, (>>=), pure, length, (<*>), fmap)

--- Proof ---
{-@ relational count2Df1 ~ count2Df2
     :: { p1:([Int] -> Bool) -> e1:Int -> l1:[[Int]] -> RTick.Tick Int
        ~ p2:([Int] -> Bool) -> e2:Int -> l2:[[Int]] -> RTick.Tick Int
        | !(true :=> true)
          :=> !(e1 = e2 && p1 = p2)
          :=> !(l1 = l2)
          :=> RTick.tcost (r1 p1 e1 l1)
            <= RTick.tcost (r2 p2 e2 l2) } @-}
--- End ---

{-@ reflect count2D @-}
count2D :: (Int -> [Int] -> Tick Int)
  -> ([Int] -> Bool)
  -> Int
  -> [[Int]]
  -> Tick Int
count2D _    _ _ [] = return 0
count2D find p x (l:m) =
  count2D find p x m >>= count2D' (p l) (find x l)

{-@ reflect count2Df1 @-}
count2Df1 :: ([Int] -> Bool) -> Int -> [[Int]] -> Tick Int
count2Df1 _ _ _      = return 0
count2Df1 p x (l:m)  = count2Df1 p x m >>= count2D' (p l) (find1 x l)

{-@ reflect count2Df2 @-}
count2Df2 :: ([Int] -> Bool) -> Int -> [[Int]] -> Tick Int
count2Df2 _ _ _      = return 0
count2Df2 p x (l:m)  = count2Df2 p x m >>= count2D' (p l) (find2 x l)


{-@ reflect count2D' @-}
count2D' :: Bool -> Tick Int -> Int -> Tick Int
count2D' b c r = if b then fmap (plus r) c else return r

{-@ reflect plus @-}
{-@ plus :: Int -> Int -> Int @-}
plus :: Int -> Int -> Int
plus x y = x + y

{-@ reflect find1 @-}
find1 :: Int -> [Int] -> Tick Int
{-@ find1 :: Int -> [Int] -> {t:RTick.Tick Int | 0 <= tcost t} @-}
find1 _ []    = return 0
find1 x (y:ys)
  | x == y    = return 1
  | otherwise = step 1 (find1 x ys)

{-@ reflect find2 @-}
{-@ find2 :: Int -> [Int] -> {t:RTick.Tick Int | 0 <= tcost t} @-}
find2 :: Int -> [Int] -> Tick Int
find2 _ []     = return 0
find2 x (y:ys) = step 1 (eqBind 0 (find2 x ys) (find2Cond (if x == y then 1 else 0)))

{-@ reflect find2Cond @-}
{-@ find2Cond :: Int -> Int -> {t:RTick.Tick Int | 0 == tcost t} @-}
find2Cond :: Int -> Int -> Tick Int
find2Cond _ 1 = return 1
find2Cond d _ = return d
