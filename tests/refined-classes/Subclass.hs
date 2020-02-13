{-@ LIQUID "--reflection" @-}
module Subclass where


class MyFunctor f where
  {-@ myfmap :: forall a b. (a -> b) -> f a -> f b @-}
  myfmap :: (a -> b) -> f a -> f b

{-@ reflect myid @-}
myid :: a -> a
myid x = x

class MyFunctor f => MyApplicative f where
  {-@ mypure :: forall a. a -> f a @-}
  mypure :: a -> f a
  {-@ myap :: forall a b. f (a -> b) -> f a -> f b @-}
  myap :: f (a -> b) -> f a -> f b
  {-@ myprop :: forall a b. x:f a -> f:(a -> b) -> {myfmap f x == myap (mypure f) x} @-}
  myprop :: f a -> (a -> b) -> ()

  
{-@ data MyId a = MyId a @-}
data MyId a = MyId a

instance MyFunctor MyId where
  myfmap f (MyId i) = MyId (f i)
  
