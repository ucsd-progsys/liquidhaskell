module Compose where

{-@ 
cmp :: forall < pref :: b -> Prop, postf :: b -> c -> Prop
              , pre  :: a -> Prop, postg :: a -> b -> Prop
              , post :: a -> c -> Prop
              >. 
       {xx::a<pre>, w::b<postg xx> |- c<postf w> <: c<post xx>}
       {ww::a<pre> |- b<postg ww> <: b<pref>}
       f:(y:b<pref> -> c<postf y>)
    -> g:(z:a<pre > -> b<postg z>)
    -> x: a<pre> -> c<post x>
@-}

cmp :: (b -> c)
    -> (a -> b)
    ->  a -> c

cmp f g x = f (g x)    



{-@ incr :: x:Nat -> {v:Nat | v == x + 1} @-}
incr :: Int -> Int
incr x = x + 1


{-@ incr2 :: x:Nat -> {v:Nat | v == x + 2} @-}
incr2 :: Int -> Int
incr2 = cmp incr incr


{-@ plus1 :: x:Nat -> {v:Nat | v == x + 20} @-}
plus1 :: Int -> Int
plus1 x = x + 20

{-@ plus2 :: x:{v:Nat | v > 10} -> {v:Nat | v == x + 22} @-}
plus2 :: Int -> Int
plus2 x = x + 22

{-@ plus42 :: x:Nat -> {v:Nat | v == x + 42} @-}
plus42 :: Int -> Int
plus42 = cmp plus2 plus1








