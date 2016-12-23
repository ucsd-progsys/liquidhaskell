module Data.Monoid where

{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--totality" @-}

import Prelude hiding (Monoid (..))

import Language.Haskell.Liquid.ProofCombinators


class VerifiedMonoid a where 
  mempty  :: a 

  mappend :: a -> a -> a 

  leftId  :: a -> Proof 
  rightId :: a -> Proof
  assoc   :: a -> a -> a -> Proof 

{-@ class VerifiedMonoid a where
    mempty  :: a 
    mappend :: a -> a -> a  
    leftId  :: x:a -> {v:Proof | mappend mempty x = x }
    rightId :: x:a -> {v:Proof | mappend x mempty = x }
    assoc   :: x:a -> y:a -> z:a -> {v:Proof | mappend x (mappend y z) = mappend (mappend x y) z}
  @-}


{-@ data List a = N | C {hd :: a, tl :: List a} @-}
data List a = N | C a (List a)

-- All these should get automated by lifting instances 

{-@ instance VerifiedMonoid (List a) where 
  assume mempty  :: {v:List a | (v = N) && (v = memptyList) };
  assume mappend :: {v:(x:List a -> y:List a
                 -> {v:List a | (v = mappendList x y) && (if (is_N x) then (v == y) else (v == C (select_C_1 x) (mappendList (select_C_2 x) y) )) })  | v == mappendList};
  leftId  :: x:List a -> {v:Proof | mappendList memptyList x = x } ;
  rightId :: x:List a -> {v:Proof | mappendList x memptyList = x } ;
  assoc   :: x:List a -> y:List a -> z:List a -> {v:Proof | mappendList x (mappendList y z) = mappendList (mappendList x y) z}
  @-}




{-@ measure mappendList :: List a -> List a -> List a @-}
{-@ measure memptyList  :: List a @-}

{-@ assume $cmempty :: {v:List a | (v = N) && (v = memptyList) } @-}

{-@ assume $cmappend :: {v:
               (x:List a -> y:List a 
            -> {v:List a | (v = mappendList x y) && (if (is_N x) then (v == y) else (v == C (select_C_1 x) (mappendList (select_C_2 x) y) )) })
            | v == mappendList} @-}


instance VerifiedMonoid (List a) where
  mempty              = N 
  mappend N ys        = ys
  mappend (C x xs) ys = C x (mappend xs ys)

  leftId  x           = mappend mempty x ==. mappend N x ==. x *** QED 


  rightId N           = mappend N mempty ==. mappend N N ==. N *** QED 
  rightId (C x xs)    = mappend (C x xs) mempty ==. C x (mappend xs N ) ==. C x xs ? rightId xs *** QED 


  assoc N ys zs 
    =   mappend N (mappend ys zs)
    ==. mappend ys zs 
    ==. mappend (mappend N ys) zs 
    *** QED 
  assoc (C x xs) ys zs 
    =   mappend (C x xs) (mappend ys zs)
    ==. C x (mappend xs (mappend ys zs))
    ==. C x (mappend (mappend xs ys) zs)
        ? assoc xs ys zs 
    ==. mappend (C x (mappend xs ys)) zs
    ==. mappend (mappend (C x xs) ys) zs
    *** QED 





