{-# LANGUAGE GADTs            #-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--ple"            @-}

module IndPred where

import Prelude hiding (sum)
import Language.Haskell.Liquid.ProofCombinators

-- | Lists ---------------------------------------------------------------------

{-@ data List [llen] @-}
data List a = Nil | Cons a (List a)

-- | List Membership -----------------------------------------------------------

data InsP a where
  Ins :: a -> List a -> List a -> InsP a

data Ins a where
  Here  :: a -> List a -> Ins a
  There :: a -> a -> List a -> List a -> Ins a -> Ins a

{-@ data Ins [insNat] a where
      Here  :: m:a -> ms:List a
            -> Prop (Ins m ms (Cons m ms))

    | There :: m:a -> n:a -> ns:List a -> mns:List a
            -> Prop (Ins m ns mns)
            -> Prop (Ins m (Cons n ns) (Cons n mns))
  @-}

-- | Permutations --------------------------------------------------------------

data PermP a where
  Perm :: List a -> List a -> PermP a

data Perm a where
  NilPerm  :: Perm a
  ConsPerm :: a -> List a -> List a -> List a -> Ins a -> Perm a -> Perm a

{-@ data Perm [permNat] a where
      NilPerm  :: Prop (Perm Nil Nil)
    | ConsPerm :: m:a -> ms:List a -> ns:List a -> mns:List a
               -> Prop (Ins m ns mns)
               -> Prop (Perm ms ns)
               -> Prop (Perm (Cons m ms) mns)
  @-}

--------------------------------------------------------------------------------

{-@ reflect sum @-}
sum :: List Int -> Int
sum Nil         = 0
sum (Cons x xs) = x + sum xs

{-@ lemma :: m:Int -> ns:List Int -> mns:List Int
          -> ins:Prop (Ins m ns mns)
          -> { m + sum ns = sum mns } / [insNat ins]
  @-}
lemma :: Int -> List Int -> List Int -> Ins Int -> ()
lemma _ _ _ (Here _ _)            = ()
lemma _ _ _ (There m n ns mns pf) = lemma m ns mns pf

{-@ theorem :: ms:List Int -> ns:List Int
            -> perm:Prop (Perm ms ns)
            -> {sum ms = sum ns} / [permNat perm]
  @-}
theorem :: List Int -> List Int -> Perm Int -> ()
theorem _ _  NilPerm
  = ()
theorem _ _ (ConsPerm m ms ns mns ins perm)
  = ( lemma m ns mns ins, theorem ms ns perm )
  *** QED

-- | BOILERPLATE ---------------------------------------------------------------

{-@ measure permNat @-}
{-@ permNat :: Perm a -> Nat @-}
permNat :: Perm a -> Int
permNat (NilPerm)              = 0
permNat (ConsPerm _ _ _ _ _ t) = 1 + permNat t

{-@ measure insNat @-}
{-@ insNat :: Ins a -> Nat @-}
insNat :: Ins a -> Int
insNat (Here _ _)        = 0
insNat (There _ _ _ _ t) = 1 + insNat t

{-@ measure llen          @-}
{-@ llen :: List a -> Nat @-}
llen :: List a -> Int
llen Nil        = 0
llen (Cons h t) = 1 + llen t

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}
