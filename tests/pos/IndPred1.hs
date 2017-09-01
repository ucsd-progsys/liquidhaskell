{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Star where

type Rel a = a -> a -> Bool

{-@ data Star [toNat] a where
      Refl :: r:Rel a -> x:a -> Prop (Star r x x)
    | Step :: r:Rel a -> x:a -> y:{a | r x y} -> z:a -> Prop (Star r y z) -> Prop (Star r x z)
  @-}

{-@ thm :: r:Rel a -> x:a -> y:a -> z:a
        -> Prop (Star r x y)
        -> Prop (Star r y z)
        -> Prop (Star r x z)
  @-}
thm r x y z (Refl _ _)          yz = yz
thm r x y z (Step _ _ x1 _ x1y) yz = Step r x x1 z (thm r x1 y z x1y yz)

--------------------------------------------------------------------------------
-- BOILERPLATE
--------------------------------------------------------------------------------

thm :: Rel a -> a -> a -> a -> Star a -> Star a -> Star a

data StarP a where
  Star :: Rel a -> a -> a -> StarP a

data Star a where
  Refl :: Rel a -> a -> Star a
  Step :: Rel a -> a -> a -> a -> Star a -> Star a

{-@ measure toNat          @-}
{-@ toNat :: Star a -> Nat @-}
toNat :: Star a -> Int
toNat (Refl _ _)       = 0
toNat (Step _ _ _ _ s) = 1 + toNat s

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}
