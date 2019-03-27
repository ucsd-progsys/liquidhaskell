{-# LANGUAGE GADTs #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--exact-data-con" @-}
module Gadt where

{-@
data Foo a <p :: Int -> Bool> where
   A :: Foo<{\_ -> True}> ()
@-}
data Foo a where
  A :: Foo ()

{-@ reflect getFoo @-}
getFoo :: Foo a -> a
getFoo A = ()