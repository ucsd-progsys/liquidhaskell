{-@ LIQUID "--no-termination" @-}

module Shapes where
 
-- https://gist.github.com/cartazio/6891549

data Shape = Nil | Cons !Int !Shape 

{-@ measure rank :: Shape -> Int
    rank (Nil)       = 0
    rank (Cons d ds) = 1 + (rank ds)
  @-}

{-@ type DIM1 = {v:Shape | (rank v) = 1} @-}
{-@ type DIM2 = {v:Shape | (rank v) = 2} @-}

{-@ oneDim :: DIM1 @-}
oneDim = 12 `Cons` Nil

{-@ twoDim :: DIM2 @-}
twoDim = 2 `Cons` (17 `Cons` Nil)

-- clearly an error, is flagged by LiquidHaskell
{-@ twoDim' :: DIM2 @-}
twoDim' = 56 `Cons` (2 `Cons` (17 `Cons` Nil))

{-@ reverseShape :: sh:Shape -> {v:Shape | (rank v) = (rank sh)} @-}
reverseShape shs = go shs Nil 
    where
        {-@ go ::  a:Shape -> b:Shape -> {v:Shape | (rank v) = (rank a) + (rank b)} @-}
        go Nil res            = res   
        go (Cons ix more) res = go more  (Cons ix res)
 
  
