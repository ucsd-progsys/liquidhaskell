module ListAnd where
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

import Prelude hiding (and, all)
import Language.Haskell.Liquid.ProofCombinators

{-@ infix : @-}

type Elm = Int


{-@ reflect and @-}
{-@ and :: x : Bool -> y : Bool -> {z : Bool | z <=> x && y } @-}
and :: Bool -> Bool -> Bool
and True  y = y
and False _ = False

{-@ reflect gte @-}
{-@ gte :: x : Elm -> y : Elm -> {z : Bool | z <=> x >= y} @-}
gte :: Elm -> Elm -> Bool
gte = (>=)

{-@ reflect lte @-}
{-@ lte :: x : Elm -> y : Elm -> {z : Bool | z <=> x <= y} @-}
lte :: Elm -> Elm -> Bool
lte = (<=)

{-@ reflect all @-}
all :: (Elm -> Bool) -> [Elm] -> Bool
all _ []        = True
all f (x : xs) = f x && all f xs

{-@ simple :: x : Elm -> y : Elm -> ys : [Elm] -> {v : () | and (lte y x) (all (gte x) ys) = all (gte x) (y:ys) } @-}
simple :: Elm -> Elm -> [Elm] -> Proof
simple x y _ = if lte y x then () else ()
 {-
       all (gte x) (y : ys)
  === (lte y x) `and` all (gte x ) ys
  -- === (gte x y) `and` all (gte x ) ys
  *** QED -}
