-- ISSUE: 
-- This file takes nearly a MINUTE when automatic-instances is off,
-- and FOREVER when automatic-instances is on.

{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--totality"                            @-}

{- LIQUID "--automatic-instances=liquidinstances" @-}

module SearchTree where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (max)

-- | Options -------------------------------------------------------------------

{-@ data Option a = None | Some a @-}
data Option a = None | Some a

-- | Maps ----------------------------------------------------------------------

{-@ data Map [size] k v =
      Leaf
    | Node { mKey   :: k
           , mVal   :: v
           , mLeft  :: Map k v
           , mRigsize :: Map k v }
  @-}

data Map k v
  = Leaf
  | Node k v (Map k v) (Map k v)

{-@ measure size @-}
{-@ size :: Map k v -> Nat @-}
size :: Map k v -> Int
size Leaf           = 0
size (Node k v l r) = 1 + size l + size r     -- TODO: silly termination error

{-@ invariant {v:Map k v | 0 <= size v } @-}

-- | Map Operations ------------------------------------------------------------

{-@ reflect get @-}

get :: (Ord k) => k -> Map k v -> Option v
get key Leaf           = None
get key (Node k v l r)
  | key == k           = Some v
  | key <  k           = get key l
  | otherwise          = get key r


{-@ reflect put @-}

put :: (Ord k) => k -> v -> Map k v -> Map k v
put key val Leaf       = Node key val Leaf Leaf
put key val (Node k v l r)
  | key == k           = Node key val l r
  | key <  k           = Node k v (put key val l) r
  | otherwise          = Node k v l (put key val r)

-- | Map Laws ------------------------------------------------------------------

{-@ thmGetEq :: (Ord k) => key:k -> val:v -> m:Map k v ->
      { get key (put key val m) = Some val }
  @-}
thmGetEq :: (Ord k) => k -> v -> Map k v -> Proof
thmGetEq key val Leaf =   get key (put key val Leaf)
                      ==. get key (Node key val Leaf Leaf)
                      ==. Some val
                      *** QED

thmGetEq key val (Node k v l r)
  | key == k          =   get key (put key val (Node k v l r))
                      ==. get key (Node key val l r)
                      ==. Some val
                      *** QED

  | key <  k          =   get key (put key val (Node k v l r))
                      ==. get key (Node k v (put key val l) r)    -- THIS LINE IS NEEDED
                      ==. get key (put key val l)
                          ? thmGetEq key val l
                      ==. Some val
                      *** QED

  | otherwise         =   get key (put key val (Node k v l r))
                      ==. get key (Node k v l (put key val r))    -- THIS LINE IS NEEDED
                      ==. get key (put key val r)
                          ? thmGetEq key val r
                      ==. Some val
                      *** QED

{-@ thmGetNeq :: (Ord k) => k1:k -> k2:{k | k1 /= k2} -> v2:v -> m:Map k v ->
      { get k1 (put k2 v2 m) = get k1 m }
  @-}
thmGetNeq :: (Ord k) => k -> k -> v -> Map k v -> Proof
thmGetNeq k1 k2 v2 Leaf
  | k1 < k2             =   get k1 (put k2 v2 Leaf)
                        ==. get k1 (Node k2 v2 Leaf Leaf)
                        ==. get k1 Leaf
                        *** QED

  | otherwise           =   get k1 (put k2 v2 Leaf)
                        ==. get k1 (Node k2 v2 Leaf Leaf)
                        ==. get k1 Leaf
                        *** QED

thmGetNeq k1 k2 v2 (Node k v l r)
  | k1 <  k, k <  k2    =   get k1 (put k2 v2 (Node k v l r))
                        ==. get k1 (Node k v l (put k2 v2 r))
                        ==. get k1 (Node k v l r)
                        *** QED

  | k1 <  k, k == k2    =   get k1 (put k2 v2 (Node k v l r))
                        ==. get k1 (Node k v2 l r)
                        ==. get k1 (Node k v l r)
                        *** QED

  | k1 == k, k <  k2    =   get k1 (put k2 v2 (Node k v l r))
                        ==. get k1 (Node k v l (put k2 v2 r))
                        ==. get k1 (Node k v l r)
                        *** QED


  | k2 <  k, k <  k1    =   get k1 (put k2 v2 (Node k v l r))
                        ==. get k1 (Node k v (put k2 v2 l) r)
                        ==. get k1 r
                        ==. get k1 (Node k v l r)
                        *** QED

  | k2 <  k, k == k1    =   get k1 (put k2 v2 (Node k v l r))
                        ==. get k1 (Node k v (put k2 v2 l) r)
                        ==. get k1 (Node k v l r)
                        *** QED

  | k2 == k, k < k1     =   get k1 (put k2 v2 (Node k v l r))
                        ==. get k1 (Node k v2 l r)
                        ==. get k1 (Node k v l r)
                        *** QED

  | k1 < k, k2 < k      =   get k1 (put k2 v2 (Node k v l r))
                        ==. get k1 (Node k v (put k2 v2 l) r)
                        ==. get k1 (put k2 v2 l)
                            ? thmGetNeq k1 k2 v2 l
                        ==. get k1 l
                        ==. get k1 (Node k v l r)
                        *** QED

  | k < k1, k < k2      =   get k1 (put k2 v2 (Node k v l r))
                        ==. get k1 (Node k v l (put k2 v2 r))
                        ==. get k1 (put k2 v2 r)
                            ? thmGetNeq k1 k2 v2 r
                        ==. get k1 r
                        ==. get k1 (Node k v l r)
                        *** QED
