{-# LANGUAGE RankNTypes #-}
-- | Tests that holes can be used for arguments and fields with a higher-rank
-- type.
module T2512 where

newtype Ur a = Ur a

{-@ flattenCallback :: f:_ -> xs:_ -> {ys:[b] | true} @-}
flattenCallback :: (forall c. ([b] -> Ur c) -> [a] -> Ur c) -> [a] -> [b]
flattenCallback f arr = case f Ur arr of Ur y -> y

{-@ app :: f:_ -> x:Int -> {v:Int | v = x} @-}
app :: (forall c. c -> c) -> Int -> Int
app f x = f x

{-@ assume appAssumed :: f:_ -> x:Int -> {v:Int | v = x} @-}
appAssumed :: (forall c. c -> c) -> Int -> Int
appAssumed f x = f x

data T = T (forall a. a -> a) Int

{-@ data T = T { tf :: _, tn :: Nat } @-}

mk :: T
mk = T id 3
