{-@ LIQUID "--expect-any-error" @-}
{-# LANGUAGE RankNTypes #-}
{-@ LIQUID "--reflection" @-}
module T1613 where

data MyFunctor f = CMyFunctor {myfmap :: forall a b. (a -> b) -> f a -> f b}


{-@ reflect myid @-}
myid :: a -> a
myid x = x

{-@ data MyApplicative f = CMyApplicative
      { p1MyApplicative :: MyFunctor f
      , myprop :: forall a b. x:f a -> f:(a -> b) -> {myid x /= x}
      } @-}

data MyApplicative f = CMyApplicative
  { p1MyApplicative :: MyFunctor f
  , myprop :: forall a b.f a -> (a -> b) -> ()
  }

data MyId a = MyId a

fMyFunctorMyId :: MyFunctor MyId
fMyFunctorMyId = CMyFunctor (\f (MyId x) -> MyId (f x))

cmyprop :: MyId a -> (a -> b) -> ()
cmyprop _ _ = ()

fMyApplicativeMyId :: MyApplicative MyId
fMyApplicativeMyId = CMyApplicative fMyFunctorMyId cmyprop
