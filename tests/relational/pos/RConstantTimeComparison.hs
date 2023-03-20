
--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
--
{-@ LIQUID "--relational-hints" @-}
{-@ LIQUID "--reflection"      @-}
{-@ LIQUID "--ple"             @-}

module RConstantTimeComparison
  (module RConstantTimeComparison) where

import Prelude hiding ( pure, return, and, fmap, length )

import RTick
import Language.Haskell.Liquid.ProofCombinators
import Lists
import Erasure

--
-- Proving a password comparisons function adheres to the
-- \"constant-time discipline\" using relational cost analysis.
--

data Bit = Zero | One deriving Eq

{-@ reflect comp @-}
{-@ comp
     :: xs:[Bit]
     -> { ys:[Bit] | length xs == length ys }
     -> { t:Tick Bool | tcost t == length xs }
@-}
comp :: [Bit] -> [Bit] -> Tick Bool
comp []       _        = return True
comp (x : xs) (y : ys) = let Tick m v = comp xs ys in
  Tick (m + 1) (and (x == y) v)

--- Proof ---
{-@ relational comp ~ comp 
      :: { xs1:[Bit] -> ys1:[Bit] -> t:Tick Bool
         ~ xs2:[Bit] -> ys2:[Bit] -> t:Tick Bool
         | !(xs1 = xs2) 
            :=> !(Lists.length xs1 == Lists.length ys1 && Lists.length xs1 == Lists.length ys2)
            :=> RTick.tcost (RConstantTimeComparison.comp xs1 ys1) 
                  == RTick.tcost (RConstantTimeComparison.comp xs1 ys2) } @-}
--- End ---

{-
Previous comp:
-> comp (x : xs) (y : ys) = pure (&& x == y) </> comp xs ys

Both this two were giving problems, I don't know why:

pure :: a -> Tick a
pure x = Tick 0 x

(</>) :: Tick (a -> b) -> Tick a -> Tick b
Tick m f </> Tick n x = Tick (1 + m + n) (f x)
-}

{-@ reflect and @-}
{-@ and :: Bool -> Bool -> Bool @-}
and :: Bool -> Bool -> Bool
and x y = x && y
