{-# LANGUAGE RankNTypes #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module SemigroupOp where
import ProofCombinators

class MySemigroup a where
    ymappend :: a -> a -> a
    {-@ lawAssociative :: v:a -> v':a -> v'':a -> {ymappend (ymappend v v') v'' == ymappend v (ymappend v' v'')} @-}
    lawAssociative :: a -> a -> a -> ()

class (MySemigroup a) => MyMonoid a where
  ymempty :: a
  {-@ lawEmpty :: x:a -> {ymappend x ymempty == x && ymappend ymempty x == x} @-}
  lawEmpty :: a -> ()


data PNat = Z | S PNat

instance MyMonoid PNat where
  ymempty = Z
  lawEmpty Z = ()
  lawEmpty (S m) = lawEmpty m


k :: a -> b -> b
k _ y = y


-- does not typecheck
{-@ assocMonoid :: MyMonoid a => a:a -> b:a -> c:a -> {ymappend a (ymappend b c) == ymappend (ymappend a b) c} @-}
assocMonoid :: MyMonoid a => a -> a -> a -> ()
assocMonoid a b c = lawAssociative a b c 

instance MySemigroup PNat where
  ymappend Z n = n
  ymappend (S m) n = S (ymappend m n)
  lawAssociative Z m n = ymappend Z (ymappend m n) `k`
                         ymappend m n `k`
                         ymappend (ymappend Z m) n `k`
                         ()
  lawAssociative (S p) m n = ymappend (S p) (ymappend m n) `k`
                             S (ymappend p (ymappend m n)) `k`
                             lawAssociative p m n `k`
                             S (ymappend (ymappend p m) n) `k`
                             ymappend (S (ymappend p m) ) n `k`
                             ymappend (ymappend (S p) m ) n `k`
                             ()

data MyList a = 
    MyNil
  | MyCons a (MyList a)


instance MySemigroup (MyList a) where
    ymappend MyNil t = t
    ymappend (MyCons v l) t = MyCons v (ymappend l t)

    -- lawAssociativity x y z = assume (mymappend x (mymappend y z) == mymappend (mymappend x y) z)
    lawAssociative MyNil _ _ = ()
    lawAssociative (MyCons x xs) y z = lawAssociative xs y z

data Op a = Op a


instance (MySemigroup a) => MySemigroup (Op a) where
  ymappend (Op x) (Op y) = Op (ymappend y x)
  lawAssociative (Op x) (Op y) (Op z) = lawAssociative z y x `cast` ()

