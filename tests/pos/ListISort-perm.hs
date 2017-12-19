{-# LANGUAGE GADTs            #-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--higherorder"    @-}

module ListSort where

import Language.Haskell.Liquid.NewProofCombinators


-- FULL SIGS: don't work right now, thanks to https://github.com/ucsd-progsys/liquidhaskell/issues/1205
{-type OList a = List <{\fld v -> v >= fld}> a @-}
{- insertSort :: (Ord a) => xs:List a -> (res :: OList a, {v:_ | prop v = Perm xs res})          @-}
{- insert     :: (Ord a) => x:a -> xs:OList a -> (res :: OList a, {v:_ | prop v = Ins x xs res}) @-}

{-@ insertSort :: (Ord a) => xs:List a -> (res :: List a, {v:_ | prop v = (Perm xs res)})         @-}
insertSort        :: (Ord a) => List a -> (List a, Perm a)
insertSort Nil         = (Nil, NilPerm)
insertSort (Cons x xs) = (xys, ConsPerm x xs ys xys x_ys_xys xs_ys)
  where
    (ys,  xs_ys)       = insertSort xs
    (xys, x_ys_xys)    = insert x ys

{-@ insert     :: (Ord a) => x:a -> xs:List a -> (res :: List a, {v:_ | prop v = (Ins x xs res)}) @-}
insert    :: (Ord a) => a -> List a -> (List a, Ins a)
insert y (Cons x xs)
  | y <= x    = (Cons y (Cons x xs), Here y (Cons x xs) )
  | otherwise = (Cons x yxs        , There y x xs yxs pf)
  where
    (yxs, pf) = insert y xs
insert y Nil  = (Cons y Nil, Here y Nil)

-- | Lists ---------------------------------------------------------------------

data List a
  = Nil
  | Cons { lHd :: a, lTl :: List a }

{-@ data List [llen] a <p :: x0:a -> x1:a -> Bool>
  = Nil
  | Cons { lHd :: a, lTl :: List <p> (a <p lHd>) }
  @-}

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
