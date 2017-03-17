{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module MaybeReflect0 where


import Prelude hiding (Maybe(..))

data Maybe a = Nothing | Just a
{-@ data Maybe a = Nothing | Just a @-}


{-@ reflect seq @-}
seq :: Maybe (a -> b) -> Maybe a -> Maybe b
seq (Just f) (Just x) = Just (f x)
seq _         _       = Nothing

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@ reflect pure @-}
pure :: a -> Maybe a
pure x = Just x
