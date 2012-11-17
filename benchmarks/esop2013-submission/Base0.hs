
module Data.Map.Base where

import Language.Haskell.Liquid.Prelude

import Prelude hiding (lookup,map,filter,foldr,foldl,null)

data Map k a  = Bin Size k a (Map k a) (Map k a)
              | Tip

data MaybeS a = NothingS | JustS a -- LIQUID: !-annot-fix

type Size     = Int

{-@ include <Base.hquals> @-}

{-@ data Map k a <l :: root:k -> k -> Bool, r :: root:k -> k -> Bool>
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


{-@ union :: (Ord k) => OMap k a -> OMap k a -> OMap k a @-}
union :: Ord k => Map k a -> Map k a -> Map k a
union Tip t2  = t2
union t1 Tip  = t1
union t1 t2 = hedgeUnion NothingS NothingS t1 t2

{- hedgeUnion :: (Ord k) => lo0:MaybeS k -> lo: {v: MaybeS {v: k | (isJustS(lo0) && (v = fromJustS(lo0))) } | v = lo0 }  
                          -> hi0:MaybeS k -> hi:{v: MaybeS {v: k | ( isJustS(hi0) && (v = fromJustS(hi0))) } 
                                                  | (((isJustS(lo) && isJustS(v)) => (fromJustS(v) >= fromJustS(lo))) && (v = hi0)) }   
                          -> OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } a 
                          -> {v: OMap k a | (((isBin(v) && isJustS(lo)) => (fromJustS(lo) < key(v))) && ((isBin(v) && isJustS(hi)) => (fromJustS(hi) > key(v)))) } 
                          ->  OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } a @-}
-- hedgeUnion :: Ord k => MaybeS k -> MaybeS k -> MaybeS k -> MaybeS k -> Map k b -> Map k b -> Map k b
-- hedgeUnion _ _ _ _  t1  Tip = t1
-- hedgeUnion blo0 blo bhi0 bhi Tip (Bin _ kx x l r) = join kx x (filterGt blo l) (filterLt bhi r)
-- hedgeUnion _ _ _ _   t1  (Bin _ kx x Tip Tip) = insertR kx x t1  -- According to benchmarks, this special case increases
--                                                                  -- performance up to 30%. It does not help in difference or intersection.
-- hedgeUnion blo0 blo bhi0 bhi (Bin _ kx x l r) t2 = join kx x (hedgeUnion blo blo bmi bmi l (trim blo bmi t2))
--                                                              (hedgeUnion bmi bmi bhi0 bhi r (trim bmi bhi t2))
--   where bmi = JustS kx

{-@ hedgeUnion :: (Ord k) => lo: {v0: MaybeS {v: k | (isJustS(v0) && (v = fromJustS(v0))) } | 0 = 0 }  
                          -> hi: {v0: MaybeS {v: k | ( isJustS(v0) && (v = fromJustS(v0))) } 
                                                   | (((isJustS(lo) && isJustS(v0)) => (fromJustS(v0) >= fromJustS(lo)))) }   
                          -> OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } a 
                          -> {v: OMap k a | (((isBin(v) && isJustS(lo)) => (fromJustS(lo) < key(v))) && ((isBin(v) && isJustS(hi)) => (fromJustS(hi) > key(v)))) } 
                          ->  OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } a @-}

-- left-biased hedge union
hedgeUnion :: Ord a => MaybeS a -> MaybeS a -> Map a b -> Map a b -> Map a b
hedgeUnion _   _   t1  Tip = t1
hedgeUnion blo bhi Tip (Bin _ kx x l r) = join kx x (filterGt blo l) (filterLt bhi r)
hedgeUnion _   _   t1  (Bin _ kx x Tip Tip) = insertR kx x t1 -- According to benchmarks, this special case increases
                                                              -- performance up to 30%. It does not help in difference or intersection.
hedgeUnion blo bhi (Bin _ kx x l r) t2 = join kx x (hedgeUnion blo bmi l (trim blo bmi t2))
                                                   (hedgeUnion bmi bhi r (trim bmi bhi t2))
  where bmi = JustS kx

{-@ filterGt :: (Ord k) => x:MaybeS k -> OMap k v -> OMap {v:k | ((isJustS(x)) => (v > fromJustS(x))) } v @-}
filterGt :: (Ord k) => MaybeS k -> Map k v -> Map k v
filterGt = error ""

{-@ filterLt :: (Ord k) => x:MaybeS k -> OMap k v -> OMap {v:k | ((isJustS(x)) => (v < fromJustS(x))) } v @-}
filterLt :: (Ord k) => MaybeS k -> Map k v -> Map k v
filterLt = error ""

{-@ insertR :: Ord k => k -> a -> OMap k a -> OMap k a @-}
insertR :: Ord k => k -> a -> Map k a -> Map k a
insertR = error ""

{-@ join :: Ord k => k -> a -> OMap k a -> OMap k a -> OMap k a @-}
join :: Ord k => k -> a -> Map k a -> Map k a -> Map k a 
join = error ""



