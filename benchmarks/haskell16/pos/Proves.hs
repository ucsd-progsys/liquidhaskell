{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE IncoherentInstances   #-}
module Proves (

    (==:), (<=:), (<:), (>:)

  , (==?)

  , (==!), (<=!), (<!), (>!), (>=!)

  , (?)

  , (==>), (&&&)

  , proof, toProof, simpleProof

  , Proof

  ) where


-- | proof operators requiring proof terms
infixl 3 ==:, <=:, <:, >:, ==?

-- | proof operators with optional proof terms
infixl 3 ==!, <=!, <!, >!, >=!

-- provide the proof terms after ?
infixl 3 ?


type Proof = ()


(?) :: (Proof -> a) -> Proof -> a
f ? y = f y


{-@ measure proofBool :: Proof -> Bool @-}

-- | Proof combinators (are Proofean combinators)
{-@ (==>) :: p:Proof
          -> q:Proof
          -> {v:Proof |
          ((Prop (proofBool p)) && (Prop (proofBool p) => Prop (proofBool q)))
          =>
          ((Prop (proofBool p) && Prop (proofBool q)))
          } @-}
(==>) :: Proof -> Proof -> Proof
p ==> q = ()


{-@ (&&&) :: p:{Proof | Prop (proofBool p) }
          -> q:{Proof | Prop (proofBool q) }
          -> {v:Proof | Prop (proofBool p) && Prop (proofBool q) } @-}
(&&&) :: Proof -> Proof -> Proof
p &&& q = ()


-- | proof goes from Int to resolve types for the optional proof combinators
proof :: Int -> Proof
proof _ = ()

toProof :: a -> Proof
toProof _ = ()

simpleProof :: Proof
simpleProof = ()

-- | Comparison operators requiring proof terms

(<=:) :: a -> a -> Proof -> a
{-@ (<=:) :: x:a -> y:a -> {v:Proof | x <= y } -> {v:a | v == x } @-}
(<=:) x y _ = x

(<:) :: a -> a -> Proof -> a
{-@ (<:) :: x:a -> y:a -> {v:Proof | x < y } -> {v:a | v == x } @-}
(<:) x y _ = x


(>:) :: a -> a -> Proof -> a
{-@ (>:) :: x:a -> y:a -> {v:Proof | x >y } -> {v:a | v == x } @-}
(>:) x _ _ = x


(==:) :: a -> a -> Proof -> a
{-@ (==:) :: x:a -> y:a -> {v:Proof| x == y} -> {v:a | v == x && v == y } @-}
(==:) x _ _ = x



-- | Comparison operators requiring proof terms optionally

class ToProve a r where
  (==?) :: a -> a -> r


instance (a~b) => ToProve a b where
{-@ instance ToProve a b where
  ==? :: x:a -> y:a -> {v:b | v ~~ x && v ~~ y}
  @-}
  (==?)  = undefined

instance (a~b) => ToProve a (Proof -> b) where
{-@ instance ToProve a (Proof -> b) where
  ==? :: x:a -> y:a -> Proof -> {v:b | v ~~ x && v ~~ y }
  @-}
  (==?) = undefined



class OptEq a r where
  (==!) :: a -> a -> r

instance (a~b) => OptEq a (Proof -> b) where
{-@ instance OptEq a (Proof -> b) where
  ==! :: x:a -> y:a -> {v:Proof | x == y} -> {v:b | v ~~ x && v ~~ y }
  @-}
  (==!) x _ _ = x

instance (a~b) => OptEq a b where
{-@ instance OptEq a b where
  ==! :: x:a -> y:{a| x == y} -> {v:b | v ~~ x && v ~~ y}
  @-}
  (==!) x _ = x


instance OptEq a a where
{-@ instance OptEq a a where
  ==! :: x:a -> y:{a| x == y} -> {v:a | v == x }
  @-}
  (==!) x _ = x

instance OptEq a (Proof -> a) where
{-@ instance OptEq a (Proof -> a) where
  ==! :: x:a -> y:a -> {v:Proof | x == y} -> {v:a | v == x }
  @-}
  (==!) x _ _ = x


class OptLEq a r where
  (<=!) :: a -> a -> r

instance OptLEq a (Proof -> a) where
{-@ instance OptLEq a (Proof -> a) where
  <=! :: x:a -> y:a -> {v:Proof| x <= y} -> {v:a | v == x && v <= y}
  @-}
  (<=!) x _ _ = x

instance OptLEq a a where
{-@ instance OptLEq a a where
  <=! :: x:a -> y:{a| x <= y} -> {v:a | v == x && v <= y }
  @-}
  (<=!) x _ = x



class OptGEq a r where
  (>=!) :: a -> a -> r

instance OptGEq a (Proof -> a) where
{-@ instance OptGEq a (Proof -> a) where
  >=! :: x:a -> y:a -> {v:Proof| x >= y} -> {v:a | v == x && v >= y}
  @-}
  (>=!) x _ _ = x

instance OptGEq a a where
{-@ instance OptGEq a a where
  >=! :: x:a -> y:{a| x >= y} -> {v:a | v == x && v >= y }
  @-}
  (>=!) x _ = x


class OptLess a r where
  (<!) :: a -> a -> r

instance OptLess a (Proof -> a) where
{-@ instance OptLess a (Proof -> a) where
  <! :: x:a -> y:a -> {v:Proof| x < y} -> {v:a | v == x && v < y}
  @-}
  (<!) x _ _ = x

instance OptLess a a where
{-@ instance OptLess a a where
  <! :: x:a -> y:{a| x < y} -> {v:a | v == x && v < y }
  @-}
  (<!) x y = x

class OptGt a r where
  (>!) :: a -> a -> r

instance OptGt a (Proof -> a) where
{-@ instance OptGt a (Proof -> a) where
  >! :: x:a -> y:a -> {v:Proof| x > y} -> {v:a | v == x && v > y}
  @-}
  (>!) x _ _ = x

instance OptGt a a where
{-@ instance OptGt a a where
  >! :: x:a -> y:{a| x > y} -> {v:a | v == x && v > y }
  @-}
  (>!) x y = x
