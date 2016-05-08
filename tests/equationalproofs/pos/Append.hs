{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--eliminate" @-}
{-@ LIQUID "--maxparams=10"  @-}
{-@ LIQUID "--higherorderqs" @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module MapFusion where

import Prelude hiding (map)

import Proves


{-@ axiomatize append @-}
append :: L a -> L a -> L a
append xs ys  
  | nill xs   = ys 
  | otherwise = C (hd xs) (append (tl xs) ys) 





prop_append_neutral :: L a -> Proof 
{-@ prop_append_neutral :: xs:L a -> {v:Proof | append xs N == xs }  @-}
prop_append_neutral N 
  = toProof $ 
       append N N ==! N 
prop_append_neutral (C x xs)
  = toProof $ 
       append (C x xs) N ==! C x (append xs N)
                         ==! C x xs             ? prop_append_neutral xs  



{-@ prop_assoc :: xs:L a -> ys:L a -> zs:L a
               -> {v:Proof | append (append xs ys) zs == append xs (append ys zs) } @-}
prop_assoc :: L a -> L a -> L a -> Proof 
prop_assoc N ys zs 
  = toProof $ 
       append (append N ys) zs ==! append ys zs
                               ==! append N (append ys zs)

prop_assoc (C x xs) ys zs 
  = toProof $ 
      append (append (C x xs) ys) zs
        ==! append (C x (append xs ys)) zs
        ==! C x (append (append xs ys) zs)
        ==! C x (append xs (append ys zs))  ? prop_assoc xs ys zs 
        ==! append (C x xs) (append ys zs)



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
{-@ tl :: xs:{L a | llen xs > 0 } -> {v:L a | llen v == llen xs - 1 } @-}
tl :: L a -> L a 
tl (C _ xs) = xs 
