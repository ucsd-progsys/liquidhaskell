{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--eliminate" @-}
{-@ LIQUID "--maxparams=10"  @-}
{-@ LIQUID "--higherorderqs" @-}


{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE FlexibleContexts    #-}


module MapFusion where

import Prelude hiding (map, (++), (.))

import Proves

{- axiomatize (++) @-}
(++) :: L a -> L a -> L a
xs ++ ys
  | llen xs == 0 = ys
  | otherwise    = C (hd xs) (tl xs ++ ys)


{- associative :: xs:L a -> ys:L a -> zs:L a
                -> {(xs ++ ys) ++ zs == xs ++ (ys ++ zs)} @-}
associative :: L a -> L a -> L a -> Proof
associative N ys zs
  = toProof $
       (N ++ ys) ++ zs ==. ys ++ zs
                       ==. N ++ (ys ++ zs)

associative (C x xs) ys zs
  = toProof $
      (C x xs ++ ys) ++ zs
        ==. (C x (xs ++ ys)) ++ zs
        ==. C x ((xs ++ ys) ++ zs)
        ==. C x (xs ++ (ys ++ zs))  ? associative xs ys zs
        ==. (C x xs) ++ (ys ++ zs)



{- axiomatize (.) @-}
(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

{-@ axiomatize map @-}
map :: (a -> b) -> L a -> L b
map f xs
  | llen xs == 0 = N
  | otherwise    = C (f (hd xs)) (map f (tl xs))


{- map_fusion :: f:(a -> a) -> g:(a -> a) -> xs:L a
   -> {map (f . g) xs == ((map f) . (map g)) (xs) } @-}
map_fusion :: (a -> a) -> (a -> a) -> L a -> Proof
map_fusion f g N
  = toProof $
      ((map f) . (map g)) N
        ==. (map f) ((map g) N)
        ==. map f (map g N)
        ==. map f N
        ==. N
        ==. map (f . g) N
map_fusion f g (C x xs)
  = toProof $
      map (f . g) (C x xs)
       ==. C ((f . g) x) (map (f . g) xs)
       ==. C ((f . g) x) ((map f . map g) xs) ? map_fusion f g xs
       ==. C ((f . g) x) (map f (map g xs))
       ==. C (f (g x)) (map f (map g xs))
       ==. map f (C (g x) (map g xs))
       ==. (map f) (C (g x) (map g xs))
       ==. (map f) (map g (C x xs))
       ==. (map f) ((map g) (C x xs))
       ==. ((map f) . (map g)) (C x xs)

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
