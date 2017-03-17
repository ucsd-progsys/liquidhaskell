{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module MaybeReflect1 where


import Prelude hiding (Maybe(..))

data Maybe a = Nothing | Just a
{-@ data Maybe a = Nothing | Just a @-}


{-@ reflect seqm @-}
seqm :: Maybe (a -> b) -> Maybe a -> Maybe b
seqm (Just f) (Just x) = Just (f x)
seqm _         _       = Nothing

{-@ reflect composem @-}
composem :: (b -> c) -> (a -> b) -> a -> c
composem f g x = f (g x)

{-@ reflect purem @-}
purem :: a -> Maybe a
purem x = Just x
