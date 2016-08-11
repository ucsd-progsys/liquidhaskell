{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--total"          @-}

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE QuasiQuotes          #-}

module LiquidR
  ( array
  , combine
  , indexNullary
   -- and,
   -- add,
   -- indexUnary,
   -- indexNAry
  ) where

import Prelude hiding (product, length)
-- import LiquidHaskell

--------------------------------------------------------------------------------
-- Basic List Refinements ------------------------------------------------------
--------------------------------------------------------------------------------

{-@ class measure size :: forall a. a -> Int @-}

{-@ instance measure size :: xs:[a] -> Int
    size []     = 0
    size (_:xs) = 1 + size xs   @-}

{-@ listLength :: xs:[a] -> {v:Nat | v = size xs} @-}
listLength :: [a] -> Int
listLength []     = 0
listLength (x:xs) = 1 + listLength xs

{-@ type ListN a N = {v:[a] | size v = N} @-}
{-@ type ListNE a = {v:[a] | size v > 0}  @-}
{-@ type Pos      = {v:Int | 0 < v}       @-}

-- Generic R Container Types ---------------------------------------------------

{-@ class R c where
      index  :: forall a. c a -> Int -> a
      length :: forall a. me:c a -> {v:Nat | v = size me}
  @-}
class R c where
  index  :: c a -> Int -> a
  length :: c a -> Int

-- A Generic Non-Empty Container -----------------------------------------------

{-@ type RNE c a = {v:c a | 0 < size v} @-}

-- Vector Instance -------------------------------------------------------------

newtype Vector a = V [a]

{-@ instance measure size :: Vector a -> Int
    size (V xs) = size xs
  @-}

instance R Vector where
  index  (V xs) i = xs `at` i
  length (V xs)   = listLength xs

at :: [a] -> Int -> a
at (x:_) 0  = x
at (_:xs) n = at xs (n-1)
at _      _ = undefined

-- Arrays ----------------------------------------------------------------------

data Array a = Array {
    shape :: [Int]
  , elems :: [a]
  }

{-@ measure product @-}
product :: [Int] -> Int
product []     = 1
product (x:xs) = x * product xs

{-@ data Array a = Array {
      shape :: ListNE Pos,
      elems :: ListN a (product shape)
    }                                     @-}

instance R Array where
  index  = undefined
  length = undefined

-- Modes -----------------------------------------------------------------------

class Mode a

type Logical = Maybe Bool
type Numeric = Maybe Int

-- | `Dim` is a refinement of `Numeric` where the values are defined

type Dim = Numeric
{-@ type Dim = {v:Numeric | isJust v} @-}

instance Mode Logical
instance Mode Numeric

class (Mode a) => IntoNumeric a where
  intoNumeric :: a -> Numeric

instance IntoNumeric Numeric where
  intoNumeric = id

instance IntoNumeric Logical where
  intoNumeric Nothing = Nothing
  intoNumeric (Just True)  = Just 1 -- (1.0 :: Double)
  intoNumeric (Just False) = Just 0 -- (0.0 :: Double)

-- Constructor for Arrays ------------------------------------------------------

array :: (R sh, R el, Mode v) => sh Dim -> el v -> Array v

{-@ array :: (R sh, R el, Mode v) => RNE sh Dim -> RNE el v -> Array v @-}
array _shape _elems = undefined

-- IndexNullary ----------------------------------------------------------------
{-@ type VectorN a N = {v:Vector a | size v = N} @-}

{-@ indexNullary :: (R c) => a:(c m) -> VectorN m (size a) @-}
indexNullary :: (R c) => c a -> (Vector a)
indexNullary _ = undefined

--------------------------------------------------------------------------------
-- Container Constructors ------------------------------------------------------
--------------------------------------------------------------------------------

{-@ append :: xs:_ -> ys:_ -> ListN _ {size xs + size ys} @-}
append :: [a] -> [a] -> [a]
append []     ys = ys
append (x:xs) ys = x : append xs ys

-- Constructor for vectors
{-@ measure lsize :: [[a]] -> Int
    lsize []     = 0
    lsize (x:xs) = size x + lsize xs
  @-}

{-@ combine :: ys:[[a]] -> ListN a (lsize ys) @-}
combine :: [[a]] ->  [a]
combine []       = []
combine (xs:xss) = append xs (combine xss)
