{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE CPP                   #-}

{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--exactdc"         @-}
{-@ LIQUID "--totality"        @-}

{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

{-@ assume withStrategy :: _ -> x:a -> {v:a | v == x } @-}

module Parallelize where 

import Prelude hiding (Monoid (..), length, drop, take, map)

import Language.Haskell.Liquid.ProofCombinators

import Control.Parallel.Strategies 




{-@ theorem :: f:(n -> m) -> i:Pos -> x:{n | i <= length x} 
  -> { map f (C (take i x) (chunk i x)) =   (C (f (take i x)) (map f (chunk i x))) 
     } / [length x] @-}
theorem :: (ChunkableMonoid n) => (n -> m) -> Pos -> n -> Proof 
theorem f i x 
  =   map f (C (take i x) (chunk i x)) 
  ==. C (f (take i x)) (map f (chunk i x)) 
  *** QED 

{-@ bar ::  ChunkableMonoid n => i:Pos -> x:{n | i <= length x } -> {v:n | v == take i x } @-}
bar ::  ChunkableMonoid n => Pos -> n -> n 
bar i x = take i x 



-------------------------------------------------------------------------------
------------- Helper Type Definitiions  ---------------------------------------
-------------------------------------------------------------------------------


type Morphism n m = n -> n -> Proof  
{-@ type Morphism n m F = x:n -> y:n -> {v:Proof | F mempty = mempty && F (mappend x y) == mappend (F x) (F y) } @-}

type Pos          = Int 
{-@ type Pos      = {v:Int | 0 < v} @-}

type Nat          = Int 
{-@ type Nat      = {v:Int | 0 <= v} @-}


-------------------------------------------------------------------------------
------------- Verified Monoid -------------------------------------------------
-------------------------------------------------------------------------------

class Monoid m where 
  mempty  :: m 
  mappend :: m -> m -> m 


{-@ class Monoid m where
    mempty  :: m 
    mappend :: m -> m -> m  
  @-}




-------------------------------------------------------------------------------
------------- Verified Chunkable Monoid ---------------------------------------
-------------------------------------------------------------------------------

class Monoid m => ChunkableMonoid m where 
  length :: m -> Nat 
  drop   :: Nat -> m -> m 
  take   :: Nat -> m -> m 


{-@ class ChunkableMonoid m where
  length :: x:m -> {v:Nat | v = length x} 
  drop   :: i:Nat -> x:{m | i <= length x} -> {v:m | length v == length x - i } 
  take   :: i:Nat -> x:{m | i <= length x} -> {v:m | length v == i }

 @-}

{-@ reflect method take @-}


{-@ axiomatize chunk @-}
{-@ chunk :: ChunkableMonoid m =>  i:Pos -> x:m 
          -> {v:L m | if (length x <= i) then (length v == 1) else 
                      (if (i == 1) then (length v == length x) else (length v < length x))}  / [length x] @-}
chunk :: ChunkableMonoid m =>  Pos -> m -> L m  
chunk i x 
  | length x <= i = C x N 
  | otherwise     = take i x `C` chunk i (drop i x)



-------------------------------------------------------------------------------
------------- List Definitions & Instances Verified Chunkable Monoid ----------
-------------------------------------------------------------------------------

data L a = N | C a (L a) deriving (Functor, Foldable, Traversable)
{-@ data L [lengthList] a = N | C {lhead :: a, ltail :: L a} @-}


{-@ axiomatize map @-}
{-@ map :: (a -> b) -> xs:L a -> {v:L b | length xs == length v}  @-}
map :: (a -> b) -> L a -> L b 
map _ N        = N 
map f (C x xs) = f x `C` map f xs 






{-@ measure lengthList @-}  
{-@ lengthList :: x:L a -> Nat @-}
lengthList :: L a -> Nat 
lengthList N        = 0 
lengthList (C _ xs) = 1 + lengthList xs



-------------------------------------------------------------------------------
------------- LIQUID HACKS ----------------------------------------------------
-------------------------------------------------------------------------------

-- | NV TODO: The following should get auto generated




{-@ assume mempty :: {v:m | v == mempty  && v == Parallelize.mempty##rTq } @-}

{-@ invariant {v:L a | length v == lengthList v} @-}

{-@ measure mappend :: a -> a -> a @-}
{-@ measure mempty  :: a @-}
{-@ measure Parallelize.mempty##rTq  :: a @-}
{-@ define Parallelize.mempty##rTq  = mempty  @-}

{-@ measure length :: m -> Int @-}
{-@ measure drop   :: Int -> m -> m @-}
{-@ measure take   :: Int -> m -> m @-}


{-@ measure parallelizeWithStrategy ::  Strategy (L m) -> (n -> m) -> (n -> n -> Proof) -> Int -> Int -> n -> m @-}
