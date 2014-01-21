module Blank where

{-@ LIQUID "--no-termination" @-}

data Vec a = V (Int -> a)

{-@ data Vec a < dom :: Int -> Prop,
                 rng :: Int -> a -> Prop >
      = V {a :: i:Int<dom> -> a <rng i>}  @-}

{-@ empty :: forall <p :: Int -> a -> Prop>. 
               Vec <{v:Int|0=1}, p> a     @-}

empty     = V $ \_ -> error "empty vector!"

{-@ set :: forall a <d :: Int -> Prop,
                     r :: Int -> a -> Prop>.
           key: Int<d> -> val: a<r key>
        -> vec: Vec<{v:Int<d>| v /= key},r> a
        -> Vec <d, r> a                     @-}
set key val (V f) = V $ \k -> if k == key 
                                then val 
                                else f k

{- loop :: forall a <p :: Int -> a -> Prop>.
        lo:Int
     -> hi:{Int | lo <= hi}
     -> base:a<p lo>
     -> f:(i:Int -> a<p i> -> a<p (i+1)>)
     -> a<p hi>                           @-}
-- loop  :: Int -> Int -> a -> (Int -> a -> a) -> a
-- loop lo hi base f = go lo base
--   where 
--     go i acc 
--       | i < hi    = go (i+1) (f i acc)
--       | otherwise = acc

{-@ loop :: forall a <p :: Int -> a -> Prop>.
        lo:Nat
     -> hi:{Nat | lo <= hi}
     -> base:Vec <{v:Nat | (v < lo)}, p> a
     -> f:(i:Nat -> Vec <{v:Nat | v < i}, p> a -> Vec <{v:Nat | v < i+1}, p> a)
     -> Vec <{v:Nat | v < hi}, p> a                          @-}
loop  :: Int -> Int -> Vec a -> (Int -> Vec a -> Vec a) -> Vec a
loop lo hi base f = go lo base
  where
    go i acc
      | i < hi    = go (i+1) (f i acc)
      | otherwise = acc

{-@ predicate Seg V I J = (I <= V && V < J) @-}

{-@ type IdVec N = Vec <{\v -> (Seg v 0 N)}, 
                        {\k v -> v=k}> 
                       Int                  @-}

{-@ initUpto :: n:Nat -> (IdVec n) @-}
initUpto n   = loop 0 n empty (\i acc -> set i i acc)

{-@ qualif Foo(v:Int): v < 0 @-}

