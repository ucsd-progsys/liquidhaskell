
module Goober where

import Language.Haskell.Liquid.Prelude

import Prelude hiding (lookup,map,filter,foldr,foldl,null)

data Map k a  = Bin Size k a (Map k a) (Map k a)
              | Tip

data MaybeS a = NothingS | JustS a -- LIQUID: !-annot-fix

type Size     = Int

{-@ include <Base.hquals> @-}

{-@ data Map [mlen] k a <l :: root:k -> k -> Prop, r :: root:k -> k -> Prop>
         = Bin (sz    :: Size) 
               (key   :: k) 
               (value :: a) 
               (left  :: Map <l, r> (k <l key>) a) 
               (right :: Map <l, r> (k <r key>) a) 
         | Tip 
  @-}

{-@ measure mlen :: (Map k a) -> Int
    mlen(Tip) = 0
    mlen(Bin s k v l r) = 1 + (mlen l) + (mlen r)
  @-}

{-@ invariant {v:Map k a | (mlen v) >= 0} @-}

{-@ type OMap k a = Map <{\root v -> v < root}, {\root v -> v > root}> k a @-}

{-@ measure isJustS :: forall a. MaybeS a -> Prop
    isJustS (JustS x)  = true
    isJustS (NothingS) = false
@-}

{-@ measure fromJustS :: forall a. MaybeS a -> a 
    fromJustS (JustS x) = x 
  @-}

{-@ measure isBin :: Map k a -> Prop
    isBin (Bin sz kx x l r) = true
    isBin (Tip)             = false
  @-}

{-@ measure key :: Map k a -> k 
    key (Bin sz kx x l r) = kx 
  @-}

{-@ invariant {v0: MaybeS {v: a | ((isJustS v0) && (v = (fromJustS v0)))} | true} @-}


{-@ trim :: (Ord k) => lo:MaybeS k 
                    -> hi:MaybeS k 
                    -> OMap k a 
                    -> {v: OMap k a | (((isBin(v) && isJustS(lo)) => (fromJustS(lo) < key(v))) && 
                                       ((isBin(v) && isJustS(hi)) => (fromJustS(hi) > key(v)))) } @-}

trim :: Ord k => MaybeS k -> MaybeS k -> Map k a -> Map k a
trim NothingS   NothingS   t = t
trim (JustS lk) NothingS   t = greater lk t 
  where greater lo t@(Bin _ k _ _ r) | k <= lo      = greater lo r
                                     | otherwise    = {- liquidAssert (k > lo) -} t
        greater _  t'@Tip                           = t'
trim NothingS   (JustS hk) t = lesser hk t 
  where lesser  hi t'@(Bin _ k _ l _) | k >= hi     = lesser  hi l
                                      | otherwise   = t'
        lesser  _  t'@Tip                           = t'
trim (JustS lk) (JustS hk) t = middle lk hk t  
  where middle lo hi t'@(Bin _ k _ l r) | k <= lo   = middle lo hi r
                                        | k >= hi   = middle lo hi l
                                        | otherwise = t'
        middle _ _ t'@Tip = t'  

delta,ratio :: Int
delta = 3
ratio = 2




size :: Map k a -> Int
size Tip              = 0
size (Bin sz _ _ _ _) = sz

{-@ bin :: k:k -> a -> OMap {v:k | v < k} a -> OMap {v:k| v > k} a -> OMap k a @-}
bin :: k -> a -> Map k a -> Map k a -> Map k a
bin k x l r
  = Bin (size l + size r + 1) k x l r


-- insertMin and insertMax don't perform potentially expensive comparisons.
{-@ insertMax, insertMin :: k -> a -> Map k a -> Map k a @-}
insertMax, insertMin :: k -> a -> Map k a -> Map k a
insertMax kx x t
  = case t of
      Tip -> singleton kx x
      Bin _ ky y l r
          -> balanceR ky y l (insertMax kx x r)

insertMin kx x t
  = case t of
      Tip -> singleton kx x
      Bin _ ky y l r
          -> balanceL ky y (insertMin kx x l) r


{-@ singleton :: k -> a -> OMap k a @-}
singleton :: k -> a -> Map k a
singleton k x = Bin 1 k x Tip Tip

{-@ balanceL :: kcut:k -> a -> OMap {v:k | v < kcut} a -> OMap {v:k| v > kcut} a -> OMap k a @-}
balanceL :: k -> a -> Map k a -> Map k a -> Map k a 
balanceL = undefined

{-@ balanceR :: kcut:k -> a -> OMap {v:k | v < kcut} a -> OMap {v:k| v > kcut} a -> OMap k a @-}
balanceR :: k -> a -> Map k a -> Map k a -> Map k a 
balanceR = undefined

{- LIQUIDTODO fromDistinctAscList :: [(k,a)]<{v: (k, a) | fst(v) > fst(fld)}> -> OMap k a -}
{-@ fromDistinctAscList :: {v: [(k, a)] | false} -> OMap k a @-}
fromDistinctAscList :: [(k,a)] -> Map k a
fromDistinctAscList xs
  = create const (length xs) xs
  where
    -- 1) use continuations so that we use heap space instead of stack space.
    -- 2) special case for n==5 to create bushier trees.
    create c 0 xs' = c Tip xs'
    create c 5 xs' = case xs' of
                       ((k1,x1):(k2,x2):(k3,x3):(k4,x4):(k5,x5):xx)
                            -> c (bin k4 x4 (bin k2 x2 (singleton k1 x1) (singleton k3 x3)) (singleton k5 x5)) xx
                       _ -> error "fromDistinctAscList create"
    create c n xs' = seq nr $ create (createR nr c) nl xs'
      where nl = n `div` 2
            nr = n - nl - 1

    createR n c l ((k,x):ys) = create (createB l k x c) n ys
    createR _ _ _ []         = error "fromDistinctAscList createR []"
    createB l k x c r zs     = c (bin k x l r) zs


