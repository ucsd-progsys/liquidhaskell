{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeFamilies          #-}

module Proves where


-- | proof operators requiring proof terms
infixl 3 ==:, <=:, <:, >:

-- | proof operators with optional proof terms
infixl 3 ==!, <=!, <!, >!, >=!

-- provide the proof terms after ?
infixl 3 ?

-- can Proof be unit?
type Proof = Bool

-- | Proof combinators (are boolean combinators)
{-@ (&&&) :: p:Proof -> q:Proof -> {v:Proof | Prop v <=> Prop p && Prop q } @-}
(&&&) :: Proof -> Proof -> Proof
p &&& q = p && q

(?) :: (Proof -> a) -> Proof -> a
f ? y = f y

{-# INLINE (?) #-}


-- | proof goes from Int to resolve types for the optional proof combinators
-- proof :: Bool -> Int -> Bool
proof :: Int -> Bool
proof _ = True

{-# INLINE proof #-}


-- | Comparison operators requiring proof terms

(<=:) :: Int -> Int -> Proof -> Int
{-@ (<=:) :: x:Int -> y:Int -> {v:Proof | x <= y } -> {v:Int | v == x } @-}
(<=:) x _ _ = x

(<:) :: Int -> Int -> Proof -> Int
{-@ (<:) :: x:Int -> y:Int -> {v:Proof | x < y } -> {v:Int | v == x } @-}
(<:) x _ _ = x

(>:) :: Int -> Int -> Proof -> Int
{-@ (>:) :: x:Int -> y:Int -> {v:Proof | x > y } -> {v:Int | v == x } @-}
(>:) x _ _ = x


(==:) :: Int -> Int -> Proof -> Int
{-@ (==:) :: x:Int -> y:Int -> {v:Proof| x == y} -> {v:Int | v == x && v == y } @-}
(==:) x _ _ = x



-- | Comparison operators requiring proof terms optionally


class OptEq a r where
  (==!) :: a -> a -> r

{-
-- | Note: The following will allow for polymorphic proof
-- | i.e., proof :: a -> Proof
-- | but now the `a~b` info does not go into the logic
-- | thus I cannot for example apply this trick to
-- | comparison operators
instance (a~b) => OptEq a (Bool -> b) where
{- instance OptEq a (Bool -> b) where
  ==! :: x:a -> y:a -> {v:Bool | x == y} -> {v:b | v ~~ x }
  @-}
  (==!) x _ _ = x
-}

instance OptEq a (Bool -> a) where
{-@ instance OptEq a (Bool -> a) where
  ==! :: x:a -> y:a -> {v:Bool | x == y} -> {v:a | v == x }
  @-}
  (==!) x _ _ = x

instance OptEq a a where
{-@ instance OptEq a a where
  ==! :: x:a -> y:{a| x == y} -> {v:a | v == x }
  @-}
  (==!) x _ = x



class OptLEq a r where
  (<=!) :: a -> a -> r

instance OptLEq a (Bool -> a) where
{-@ instance OptLEq a (Bool -> a) where
  <=! :: x:a -> y:a -> {v:Bool| x <= y} -> {v:a | v == x && v <= y}
  @-}
  (<=!) x _ _ = x

instance OptLEq a a where
{-@ instance OptLEq a a where
  <=! :: x:a -> y:{a| x <= y} -> {v:a | v == x && v <= y }
  @-}
  (<=!) x _ = x


class OptLess a r where
  (<!) :: a -> a -> r

instance OptLess a (Bool -> a) where
{-@ instance OptLess a (Bool -> a) where
  <! :: x:a -> y:a -> {v:Bool| x < y} -> {v:a | v == x && v < y}
  @-}
  (<!) x _ _ = x

instance OptLess a a where
{-@ instance OptLess a a where
  <! :: x:a -> y:{a| x < y} -> {v:a | v == x && v < y }
  @-}
  (<!) x _ = x



class OptGt a r where
  (>!) :: a -> a -> r

instance OptGt a (Bool -> a) where
 {-@ instance OptGt a (Bool -> a) where
    >! :: x:a -> y:a -> {v:Bool| x > y} -> {v:a | v == x && v > y}
  @-}
  (>!) x _ _ = x

instance OptGt a a where
{-@ instance OptGt a a where
    >! :: x:a -> y:{a| x > y} -> {v:a | v == x && v > y }
    @-}
  (>!) x _ = x


class OptGtEq a r where
   (>=!) :: a -> a -> r

instance OptGtEq a (Bool -> a) where
  {-@ instance OptGtEq a (Bool -> a) where
    >=! :: x:a -> y:a -> {v:Bool| x >= y} -> {v:a | v == x && v >= y}
   @-}
   (>=!) x _ _ = x

instance OptGtEq a a where
{-@ instance OptGtEq a a where
    >=! :: x:a -> y:{a| x >= y} -> {v:a | v == x && v >= y }
  @-}
  (>=!) x _ = x
