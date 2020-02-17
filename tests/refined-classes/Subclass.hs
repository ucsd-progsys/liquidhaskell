{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Subclass where

class MyFunctor f where
  {-@ myfmap :: forall a b. (a -> b) -> f a -> f b @-}
  myfmap :: (a -> b) -> f a -> f b
  (<$) :: a -> f b -> f a

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
  x <$ (MyId _) = MyId x
  
instance MyApplicative MyId where
  mypure = MyId
  myap (MyId f) (MyId a) = MyId (f a)
  myprop _ _ = ()

data Optional a = None | Has a

instance MyFunctor Optional where
  myfmap _ None = None
  myfmap f (Has x) = Has (f x)
  _ <$ None = None
  x <$ (Has _) = Has x

instance MyApplicative Optional where
  mypure = Has
  myap None _ = None
  myap _ None = None
  myap (Has f) (Has x) = Has (f x)
  myprop _ _ = ()

{-@ impl :: x:Bool -> y:Bool -> {v:Bool | v <=> (x => y)} @-}
impl :: Bool -> Bool -> Bool
impl a b = if a then b else True

{-@ reflect ffmap @-}
ffmap :: MyFunctor f => (a -> b) -> f a -> f b
ffmap = myfmap

{-@ trivial :: MyFunctor f => f:(a -> b) -> x:f a -> {myfmap f x == ffmap f x} @-}
trivial :: MyFunctor f => (a -> b) -> f a -> ()
trivial _ _ = ()
