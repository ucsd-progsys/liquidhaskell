module Foo where

{-@ LIQUID "--totality" @-}


data F a b = F {fx :: a, fy :: b} | G {fx :: a}
{-@ data F a b = F {fx :: a, fy :: b} | G {fx :: a} @-}

{-@ measure isF :: F a b -> Prop
    isF (F x y) = true
    isF (G x)   = false
  @-}

-- Record's selector type is defaulted to true as imported
{-@ fy  :: {v:F a b | (isF v)} -> b @-}
{-@ bar :: {v:F a b | (isF v)} -> b @-}
bar :: F a b  -> b
bar = fy
