module Constraints where

{-@
cmp :: forall < pref :: b -> Bool, postf :: b -> c -> Bool
              , pre  :: a -> Bool, postg :: a -> b -> Bool
              , post :: a -> c -> Bool
              >.
       {xx::a<pre>,  w::b<postg xx> |- c<postf w> <: c<post xx>}
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


{-@ incr2 :: x:Nat -> {v:Nat | v == x + 3} @-}
incr2 :: Int -> Int
incr2 = cmp incr incr
