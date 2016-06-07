{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorderqs" @-}


{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE FlexibleContexts    #-}


module MapFusion where

import Prelude hiding (map)

import Proves

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@ axiomatize map @-}
map :: (a -> b) -> L a -> L b
map f xs
  | llen xs == 0 = N
  | otherwise    = C (f (hd xs)) (map f (tl xs))


{-@ map_fusion :: f:(a -> a) -> g:(a -> a) -> xs:L a
   -> {map (compose f g) xs == (compose (map f) (map g)) (xs) } @-}
map_fusion :: (a -> a) -> (a -> a) -> L a -> Proof
map_fusion f g N
  = (compose (map f) (map g)) N
        ==! (map f) (map g N)
--         ==! map f (map g N)
        ==! map f N
        ==! N
        ==! map (compose f g) N
        *** QED
map_fusion f g (C x xs)
  = map (compose f g) (C x xs)
       ==! C ((compose f g) x) (map (compose f g) xs)
       ==! C ((compose f g) x) ((compose (map f) (map g)) xs) ? map_fusion f g xs
       ==! C ((compose f g) x) (map f (map g xs))
       ==! C (f (g x)) (map f (map g xs))
       ==! map f (C (g x) (map g xs))
       ==! (map f) (C (g x) (map g xs))
       ==! (map f) (map g (C x xs))
       ==! (map f) ((map g) (C x xs))
       ==! (compose (map f) (map g)) (C x xs)
       *** QED

data L a = N | C a (L a)
{-@ data L [llen] @-}

{-@ measure nill @-}
nill :: L a -> Bool
nill N = True
nill _ = False

{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen N        = 0
llen (C _ xs) = 1 + llen xs

{-@ measure hd @-}
{-@ hd :: {v:L a | llen v > 0 } -> a @-}
hd :: L a -> a
hd (C x _) = x


{-@ measure tl @-}
{-@ tl :: xs:{v:L a | llen v > 0 } -> {v:L a | llen v == llen xs - 1 } @-}
tl :: L a -> L a
tl (C _ xs) = xs
