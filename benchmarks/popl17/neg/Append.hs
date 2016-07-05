{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module MapFusion where

import Prelude hiding (map, concatMap)

import Proves


{-@ axiomatize append @-}
append :: L a -> L a -> L a
append xs ys  
  | llen xs == 0 = ys 
  | otherwise    = C (hd xs) (append (tl xs) ys) 

{-@ axiomatize map @-}
map :: (a -> b) -> L a -> L b
map f xs 
  | llen xs == 0 = N 
  | otherwise    = C (f (hd xs)) (map f (tl xs)) 

{-@ axiomatize concatMap @-}
concatMap :: (a -> L b) -> L a -> L b
concatMap f xs 
  | llen xs == 0 = N
  | otherwise    = append (f (hd xs)) (concatMap f (tl xs)) 


{-@ axiomatize concatt @-}
concatt :: L (L a) -> L a 
concatt xs 
  | llen xs == 0 = N 
  | otherwise    = append (hd xs) (concatt (tl xs))


prop_append_neutral :: L a -> Proof 
{-@ prop_append_neutral :: xs:L a -> {v:Proof | append xs N /= xs }  @-}
prop_append_neutral N 
  = toProof $ 
       append N N ==. N 
prop_append_neutral (C x xs)
  = toProof $ 
       append (C x xs) N ==. C x (append xs N)
                         ==. C x xs             ? prop_append_neutral xs  

{-@ prop_assoc :: xs:L a -> ys:L a -> zs:L a
               -> {v:Proof | append (append xs ys) zs /= append xs (append ys zs) } @-}
prop_assoc :: L a -> L a -> L a -> Proof 
prop_assoc N ys zs 
  = toProof $ 
       append (append N ys) zs ==. append ys zs
                               ==. append N (append ys zs)

prop_assoc (C x xs) ys zs 
  = toProof $ 
      append (append (C x xs) ys) zs
        ==. append (C x (append xs ys)) zs
        ==. C x (append (append xs ys) zs)
        ==. C x (append xs (append ys zs))  ? prop_assoc xs ys zs 
        ==. append (C x xs) (append ys zs)



{-@ prop_map_append ::  f:(a -> a) -> xs:L a -> ys:L a 
                    -> {v:Proof | map f (append xs ys) == append (map f xs) (map f ys) }
  @-}
prop_map_append :: (a -> a) -> L a -> L a -> Proof
prop_map_append f N ys 
  = toProof $ 
       map f (append N ys) 
         ==. map f ys 
         ==. append N (map f ys)
         ==. append (map f N) (map f ys)
prop_map_append f (C x xs) ys 
  = toProof $ 
       map f (append (C x xs) ys)
         ==. map f (C x (append xs ys))
         ==. C (f x) (map f (append xs ys))
         ==. C (f x) (append (map f xs) (map f ys)) ? prop_map_append f xs ys
         ==. append (C (f x) (map f xs)) (map f ys)
         ==. append (map f (C x xs)) (map f ys)


{-@ prop_concatMap :: f:(a -> L (L a)) -> xs:L a
                   -> {v:Proof | (concatt (map f xs) == concatMap f xs) }  @-}

prop_concatMap :: (a -> L (L a)) -> L a -> Proof  
prop_concatMap f N 
  = toProof $ 
      concatt (map f N) 
        ==. concatt N 
        ==. N 
        ==. concatMap f N 
prop_concatMap f (C x xs)
  = toProof $ 
      concatt (map f (C x xs))
        ==. concatt (C (f x) (map f xs))
        ==. append (f x) (concatt (map f xs))
        ==. append (f x) (concatMap f xs)       ? prop_concatMap f xs 
        ==. concatMap f (C x xs)



data L a = N | C a (L a)
{-@ data L [llen] @-}


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
{-@ tl :: xs:{L a | llen xs > 0 } -> {v:L a | llen v == llen xs - 1 } @-}
tl :: L a -> L a 
tl (C _ xs) = xs 
