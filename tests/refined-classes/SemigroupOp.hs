{-# LANGUAGE RankNTypes #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--extensionality" @-}
{-@ LIQUID "--ple" @-}
module SemigroupOp where


{-@ reflect myid @-}
myid :: a -> a
myid x = x

class MyFunctor f where
  {-@ myfmap :: forall a b.(a -> b) -> f a -> f b @-}
  myfmap :: (a -> b) -> f a -> f b
  {-@ myfmapProp :: forall a. x:f a -> {myfmap myid x == myid x}@-}
  myfmapProp :: f a -> ()

{-@ data MyId a = MyId a @-}
data MyId a = MyId a

{-@ reflect cmyfmap @-}
cmyfmap :: (a -> b) -> MyId a -> MyId b
cmyfmap f (MyId a) = MyId (f a)

{-@ myfmap2 :: MyFunctor g => f:(a -> b) -> x:g a -> {vv: g b | fmap f x = fmap g  }  @-}
myfmap2 :: MyFunctor g => (a -> b) -> g a -> g b
myfmap2 = myfmap


-- $fMyFunctor :: MyFunctor MyId
instance MyFunctor MyId where
  myfmap f (MyId a) = MyId (f a)
  myfmapProp (MyId a) = ()

{-@ reflect myConst @-}
myConst :: a -> b -> a
myConst x _ = x


k :: a -> b -> b
k _ y = y

-- yes this would fail
{-@ replaceProp :: MyFunctor f => x:a -> y:f b -> z:f c -> {myfmap (myConst x) y == myfmap  (myConst x) z} @-}
replaceProp :: MyFunctor f => a ->  f b -> f c -> ()
replaceProp x _ _ = ()


-- {-@ msame :: f:(a -> b) -> x:MyId a -> {myfmap f x == cmyfmap f x} @-}
-- msame :: (a -> b) -> MyId a -> ()
-- msame x y = cmyfmap x y `k` myfmap x y `k` ()

class YYSemigroup a where
    univ :: b -> a -> ()
    ymappend :: a -> a -> a
    {-@ lawAssociative :: v:a -> v':a -> v'':a -> {ymappend (ymappend v v') v'' == ymappend v (ymappend v' v'')} @-}
    lawAssociative :: a -> a -> a -> ()

data Op a = Op a

{-@ reflect mappendOp @-}
mappendOp :: (YYSemigroup a) => Op a -> Op a -> Op a
mappendOp (Op x) (Op y) = Op (ymappend y x)

{-@ lawAssociativeOp :: YYSemigroup a => v:Op a -> v':Op a -> v'':Op a -> {mappendOp (mappendOp v v') v'' == mappendOp v (mappendOp v' v'') }@-}
lawAssociativeOp :: YYSemigroup a => Op a -> Op a -> Op a -> ()
lawAssociativeOp (Op x) (Op y) (Op z) = lawAssociative z y x

{-@ mylawAssociative :: YYSemigroup a => v:a -> v':a -> v'':a -> {ymappend (ymappend v v') v'' == ymappend v (ymappend v' v'')}  @-}
mylawAssociative :: YYSemigroup a => a -> a -> a -> ()
mylawAssociative x y z = lawAssociative x y z

instance (YYSemigroup a) => YYSemigroup (Op a) where
  univ _ _ = ()
  ymappend = mappendOp 
  lawAssociative x y z = lawAssociativeOp x y z
