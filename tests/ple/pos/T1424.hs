-- LH#1424 
-- ISSUE: what is the "sort" for `ty` ? is is `bob` -- NO! because then sometimes `funky Field y == y :: Bool`
-- which makes SMT unhappy; is it `Bool` NO! because in the other case it CAN be an `int` which would make SMT unhappy. SIGH.

{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module T1424 where

---------------------------------------------------------------

data Field a where
  FInt  :: Field Int
  FBool :: Field Bool

---------------------------------------------------------------

{-@ reflect funky @-}
funky :: Field a -> a -> Bool
funky FInt  _   = False
funky FBool kkk = not kkk

{-@ test1 :: xig:_ -> yong:_ -> {v:_ | v == funky xig yong} @-}
test1 :: Field bob -> bob -> Bool
test1 tx ty = funky tx ty

---------------------------------------------------------------

{-@ reflect proj @-}
proj :: Field a -> a -> a 
proj FInt  nnn = add nnn 1
proj FBool kkk = not kkk

{-@ reflect add @-}
add :: Int -> Int -> Int 
add x y = x + y

{-@ test2 :: _ -> TT @-}
test2 :: () -> Bool
test2 _ = proj FInt 10 == 11

---------------------------------------------------------------

{-@ projW :: f:_ -> x:_ -> { v:_ | v = proj f x } @-}
projW :: Field a -> a -> a 
projW f x = proj f x

{-@ test3 :: _ -> TT @-}
test3 :: () -> Bool
test3 _ = projW FInt 100 == 101




