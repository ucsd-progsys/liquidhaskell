-- Ensure that rewrites work with polymorphic types

{-# LANGUAGE Rank2Types #-}

{-@ LIQUID "--extensionality" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--rw-termination-check" @-}
module ReWrite2 where

data OurMonad m = OurMonad {
  bind :: forall a b. m a -> (a -> m b) -> m b,
  return :: forall a.   a -> m a
}

{-@
data OurMonad m = OurMonad {
  bind   :: forall a b. m a -> (a -> m b) -> m b,
  return :: forall a.   a -> m a
}
@-}

{-@ reflect kleisli @-}
{-@ kleisli :: om : OurMonad m
            ->  f : (a -> m b)
            ->  g : (b -> m c)
            ->  x : a
            -> {v : m c | v = kleisli om f g x} @-}
kleisli :: OurMonad m -> (a -> m b) -> (b -> m c) -> a -> m c
kleisli om f g x = bind om (f x) g

{-@ kp :: om : OurMonad m
            ->  f : (a -> m b)
            ->  g : (b -> m c)
            ->  x : a
            -> {v : () | kleisli om f g x = bind om (f x) g} @-}
kp :: OurMonad m -> (a -> m b) -> (b -> m c) -> a -> ()
kp om f g x = ()

{-@ reflect lhs @-}
lhs om f g x = kleisli om f g x

{-@ reflect rhs @-}
rhs om f g x = bind om (f x) g

{-@ rewriteWith mp [kp] @-}
{-@ mp :: om : OurMonad m
            ->  f : (a -> m b)
            ->  g : (b -> m c)
            ->  x : a
            -> { lhs om f g x = rhs om f g x } @-}
mp :: OurMonad m -> (a -> m b) -> (b -> m c) -> a -> ()
mp om f g x = ()
