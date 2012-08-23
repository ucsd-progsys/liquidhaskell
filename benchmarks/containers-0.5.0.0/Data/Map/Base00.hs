module Foo (
              Map(..)          -- instance Eq,Show,Read
            , trim
           ) where

data Map k a  = Bin Size k a (Map k a) (Map k a)
              | Tip

data MaybeS a = NothingS | JustS a -- LIQUID: !-annot-fix

type Size     = Int

{-@ include <Base.hquals> @-}

{-@ 
  data Map k a <l :: root:k -> k -> Bool, r :: root:k -> k -> Bool>
       = Bin (sz    :: Size) 
             (key   :: k) 
             (value :: a) 
             (left  :: Map <l, r> (k <l key>) a) 
             (right :: Map <l, r> (k <r key>) a) 
       | Tip 
  @-}

{-@ type OMap k a = Map <{v:k | v < root}, {v:k | v > root}> k a @-}

{-@ measure isJustS :: forall a. MaybeS a -> Bool 
    isJustS (JustS x)  = true
    isJustS (NothingS) = false
  @-}

{-@ measure fromJustS :: forall a. MaybeS a -> a 
    fromJustS (JustS x) = x 
  @-}

{-@ measure isBin :: Map k a -> Bool
    isBin (Bin sz kx x l r) = true
    isBin (Tip)             = false
  @-}

{-@ measure key :: Map k a -> k 
    key (Bin sz kx x l r) = kx 
  @-}

{-@ trim :: (Ord k) => lo:MaybeS k 
                    -> hi:MaybeS k 
                    -> OMap k a 
                    -> {v: OMap k a | (((isBin(v) && isJustS(lo)) => (fromJustS(lo) < key(v))) && 
                                       ((isBin(v) && isJustS(hi)) => (fromJustS(hi) > key(v)))) } @-}

trim :: Ord k => MaybeS k -> MaybeS k -> Map k a -> Map k a
trim NothingS   NothingS   t = t
trim (JustS lk) NothingS   t = greater lk t 
  where greater lo t@(Bin _ k _ _ r) | k <= lo      = greater lo r
                                     | otherwise    = t
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

