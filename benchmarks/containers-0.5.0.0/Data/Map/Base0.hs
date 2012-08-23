{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
#if __GLASGOW_HASKELL__
-- LIQUID {- LANGUAGE DeriveDataTypeable, StandaloneDeriving -}
#endif
#if !defined(TESTING) && __GLASGOW_HASKELL__ >= 703
{-# LANGUAGE Trustworthy #-}
#endif

module Data.Map.Base where

import Language.Haskell.Liquid.Prelude

import Prelude hiding (lookup,map,filter,foldr,foldl,null)
import Data.Monoid (Monoid(..))
import Data.Traversable (Traversable(traverse))
import qualified Data.Foldable as Foldable
import Control.DeepSeq (NFData(rnf))

#if __GLASGOW_HASKELL__
import GHC.Exts ( build )
import Text.Read
import Data.Data
#endif

#define STRICT_1_OF_2(fn) fn arg _ | arg `seq` False = undefined
#define STRICT_1_OF_3(fn) fn arg _ _ | arg `seq` False = undefined
#define STRICT_2_OF_3(fn) fn _ arg _ | arg `seq` False = undefined
#define STRICT_1_OF_4(fn) fn arg _ _ _ | arg `seq` False = undefined
#define STRICT_2_OF_4(fn) fn _ arg _ _ | arg `seq` False = undefined

data Map k a  = Bin Size k a (Map k a) (Map k a)
              | Tip

type Size     = Int

data MaybeS a = NothingS | JustS a

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

{-@ measure isJustS :: forall a. MaybeS a -> Bool 
    isJustS (JustS x)  = true
    isJustS (NothingS) = false
  @-}

{-@ measure fromJustS :: forall a. MaybeS a -> a
    fromJustS (JustS x) = x 
  @-}

{-@ type OMap k a = Map <{v:k | v < root}, {v:k | v > root}> k a @-}

{-@ measure isBin :: Map k a -> Bool
    isBin (Bin sz kx x l r) = true
    isBin (Tip)             = false
  @-}

{-@ measure key :: Map k a -> k 
    key (Bin sz kx x l r) = kx 
  @-}

---------------------------------------------------------------------

{-@ trim :: (Ord k) => lo:MaybeS k -> hi:MaybeS k -> OMap k a -> {v: OMap k a | (((isBin(v) && isJustS(lo)) => (fromJustS(lo) < key(v))) && ((isBin(v) && isJustS(hi)) => (fromJustS(hi) > key(v)))) } @-}

trim :: Ord k => MaybeS k -> MaybeS k -> Map k a -> Map k a
trim = error "GOO"
--trim NothingS   NothingS   t = t
--trim (JustS lk) NothingS   t = greater lk t 
--  where greater lo t@(Bin _ k _ _ r) | k <= lo      = greater lo r
--                                     | otherwise    = t
--        greater _  t'@Tip                           = t'
--trim NothingS   (JustS hk) t = lesser hk t 
--  where lesser  hi t'@(Bin _ k _ l _) | k >= hi     = lesser  hi l
--                                      | otherwise   = t'
--        lesser  _  t'@Tip                           = t'
--trim (JustS lk) (JustS hk) t = middle lk hk t  
--  where middle lo hi t'@(Bin _ k _ l r) | k <= lo   = middle lo hi r
--                                        | k >= hi   = middle lo hi l
--                                        | otherwise = t'
--        middle _ _ t'@Tip = t'  

{-@ filterGt :: (Ord k) -> x:MaybeS k -> OMap k v -> OMap {v:k | ((isJustS(x)) => (v > fromJustS(x))) } v @-}
filterGt :: Ord k => MaybeS k -> Map k v -> Map k v
filterGt = error "GOO"

{-@ filterLt :: (Ord k) -> x:MaybeS k -> OMap k v -> OMap {v:k | ((isJustS(x)) => (v < fromJustS(x))) } v @-}
filterLt :: Ord k => MaybeS k -> Map k v -> Map k v
filterLt = error "GOO"

{-@ join :: kcut:k -> a -> OMap {v:k | v < kcut} a -> OMap {v:k| v > kcut} a -> OMap k a @-}
join :: k -> a -> Map k a -> Map k a -> Map k a
join kx x l r = Bin 1 kx x l r 

{-@ merge :: kcut:k -> OMap {v:k | v < kcut} a -> OMap {v:k| v > kcut} a -> OMap k a @-}
merge :: k -> Map k a -> Map k a -> Map k a
merge = error "gOO"

{-@ member :: Ord k => k -> OMap k a -> Bool @-}
member :: Ord k => k -> Map k a -> Bool 
member kx t = error "TODO"

{-@ insertR :: Ord k => k -> a -> OMap k a -> OMap k a @-}
insertR :: Ord k => k -> a -> Map k a -> Map k a
insertR kx x t = error "TODO"

{-@ singleton :: k -> a -> OMap k a @-}
singleton :: k -> a -> Map k a
singleton = error "GOO"

{-@ assert lookup :: (Ord k) => k -> OMap k a -> Maybe a @-}
lookup :: Ord k => k -> Map k a -> Maybe a
lookup = error "TDA"


{-@ hedgeDiff  :: (Ord k) => lo0:MaybeS k -> lo: {v: MaybeS {v: k | (isJustS(lo0) && (v = fromJustS(lo0))) } | v = lo0 }  
                          -> hi0:MaybeS k -> hi:{v: MaybeS {v: k | ( isJustS(hi0) && (v = fromJustS(hi0))) } 
                                                  | (((isJustS(lo) && isJustS(v)) => (fromJustS(v) >= fromJustS(lo))) && (v = hi0)) }   
                          
                          -> {v: OMap k a | (((isBin(v) && isJustS(lo)) => (fromJustS(lo) < key(v))) && ((isBin(v) && isJustS(hi)) => (fromJustS(hi) > key(v)))) } 
                          -> OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } b 
                          ->  OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } a @-}

hedgeDiff :: Ord a => MaybeS a -> MaybeS a -> MaybeS a -> MaybeS a -> Map a b -> Map a c -> Map a b
hedgeDiff _ _ _  _   Tip              _          = Tip
hedgeDiff blo0 blo bhi0 bhi (Bin _ kx x l r) Tip = join kx x (filterGt blo l) (filterLt bhi r)
hedgeDiff blo0 blo bhi0 bhi t (Bin _ kx _ l r)   = merge kx (hedgeDiff blo0 blo bmi bmi (trim blo bmi t) l)
                                                            (hedgeDiff bmi bmi bhi0 bhi (trim bmi bhi t) r)
  where bmi = JustS kx
------------------------------------------------------------------------------
-- {- hedgeUnion :: (Ord k) => lo0:MaybeS k -> lo: {v: MaybeS {v: k | (isJustS(lo0) && (v = fromJustS(lo0))) } | v = lo0 }  
--                           -> hi0:MaybeS k -> hi:{v: MaybeS {v: k | ( isJustS(hi0) && (v = fromJustS(hi0))) } 
--                                                   | (((isJustS(lo) && isJustS(v)) => (fromJustS(v) >= fromJustS(lo))) && (v = hi0)) }   
--                           -> OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } a 
--                           -> {v: OMap k a | (((isBin(v) && isJustS(lo)) => (fromJustS(lo) < key(v))) && ((isBin(v) && isJustS(hi)) => (fromJustS(hi) > key(v)))) } 
--                           ->  OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } a @-}
-- 
-- hedgeUnion :: Ord k => MaybeS k -> MaybeS k -> MaybeS k -> MaybeS k -> Map k b -> Map k b -> Map k b
-- hedgeUnion _ _ _ _  t1  Tip = t1
-- hedgeUnion blo0 blo bhi0 bhi Tip (Bin _ kx x l r) = join kx x (filterGt blo l) (filterLt bhi r)
-- hedgeUnion _ _ _ _   t1  (Bin _ kx x Tip Tip) = insertR kx x t1  -- According to benchmarks, this special case increases
--                                                                  -- performance up to 30%. It does not help in difference or intersection.
-- hedgeUnion blo0 blo bhi0 bhi (Bin _ kx x l r) t2 = join kx x (hedgeUnion blo blo bmi bmi l (trim blo bmi t2))
--                                                              (hedgeUnion bmi bmi bhi0 bhi r (trim bmi bhi t2))
--   where bmi = JustS kx
-- 
-- {- hedgeInt   :: (Ord k) => lo0:MaybeS k -> lo: {v: MaybeS {v: k | (isJustS(lo0) && (v = fromJustS(lo0))) } | v = lo0 }  
--                           -> hi0:MaybeS k -> hi:{v: MaybeS {v: k | ( isJustS(hi0) && (v = fromJustS(hi0))) } 
--                                                   | (((isJustS(lo) && isJustS(v)) => (fromJustS(v) >= fromJustS(lo))) && (v = hi0)) }   
--                           -> OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } a 
--                           -> {v: OMap k b | (((isBin(v) && isJustS(lo)) => (fromJustS(lo) < key(v))) && ((isBin(v) && isJustS(hi)) => (fromJustS(hi) > key(v)))) } 
--                           ->  OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } a @-}
-- hedgeInt :: Ord k => MaybeS k -> MaybeS k -> MaybeS k -> MaybeS k -> Map k a -> Map k b -> Map k a
-- hedgeInt _ _ _ _ _   Tip = Tip
-- hedgeInt _ _ _ _ Tip _   = Tip
-- hedgeInt blo0 blo bhi0 bhi (Bin _ kx x l r) t2 = let l' = hedgeInt blo0 blo bmi bmi  l (trim blo bmi t2)
--                                                      r' = hedgeInt bmi bmi bhi0 bhi  r (trim bmi bhi t2)
--                                                  in if kx `member` t2 then join kx x l' r' else merge kx l' r'
--   where bmi = JustS kx
----------------------------------------------------------------------------------

{- mergeWithKey :: (Ord k) => (k -> a -> b -> Maybe c) 
                          -> (lo:MaybeS k -> hi: MaybeS k 
                              -> OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } a
                              -> OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } c) 
                          -> (lo:MaybeS k -> hi: MaybeS k 
                              -> OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } b
                              -> OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } c) 
                          -> OMap k a -> OMap k b -> OMap k c @-}
--mergeWithKey :: Ord k => (k -> a -> b -> Maybe c) -> (MaybeS k -> MaybeS k -> Map k a -> Map k c) -> (MaybeS k -> MaybeS k -> Map k b -> Map k c)
--             -> Map k a -> Map k b -> Map k c
--mergeWithKey f g1 g2 = go
--  where
--    go Tip t2 = g2 NothingS NothingS t2
--    go t1 Tip = g1 NothingS NothingS t1
--    go t1 t2  = hedgeMerge f g1 g2 NothingS NothingS NothingS NothingS t1 t2

{-@ hedgeMerge :: (Ord k) => (k -> a -> b -> Maybe c) 
                          -> (lo:MaybeS k -> hi: MaybeS k 
                              -> OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } a
                              -> OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } c) 
                          -> (lo:MaybeS k -> hi: MaybeS k 
                              -> OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } b
                              -> OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } c) 
                          -> lo0:MaybeS k -> lo: {v: MaybeS {v: k | (isJustS(lo0) && (v = fromJustS(lo0))) } | v = lo0 }  
                          -> hi0:MaybeS k -> hi:{v: MaybeS {v: k | ( isJustS(hi0) && (v = fromJustS(hi0))) } 
                                                  | (((isJustS(lo) && isJustS(v)) => (fromJustS(v) >= fromJustS(lo))) && (v = hi0)) }   
                          -> OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } a 
                          -> {v: OMap k b | (((isBin(v) && isJustS(lo)) => (fromJustS(lo) < key(v))) && ((isBin(v) && isJustS(hi)) => (fromJustS(hi) > key(v)))) } 
                          ->  OMap {v: k | (((isJustS(lo)) => (v > fromJustS(lo))) && (((isJustS(hi)) => (v < fromJustS(hi))))) } c @-}

hedgeMerge :: Ord k => (k -> a -> b -> Maybe c) 
                    -> (MaybeS k -> MaybeS k -> Map k a -> Map k c) 
                    -> (MaybeS k -> MaybeS k -> Map k b -> Map k c)
                    -> MaybeS k -> MaybeS k -> MaybeS k -> MaybeS k 
                    -> Map k a -> Map k b -> Map k c
hedgeMerge f g1 g2 _ blo _  bhi   t1  Tip 
  = g1 blo bhi t1
hedgeMerge f g1 g2 blo0 blo bhi0 bhi Tip (Bin _ kx x l r) 
  = g2 blo bhi $ join kx x (filterGt blo l) (filterLt bhi r)
hedgeMerge f g1 g2 blo0 blo bhi0 bhi (Bin _ kx x l r) t2  
  = let bmi = JustS kx 
        l' = hedgeMerge f g1 g2 blo0 blo bmi bmi l (trim blo bmi t2)
        (found, trim_t2) = trimLookupLo kx bhi t2
        r' = hedgeMerge f g1 g2 bmi bmi bhi0 bhi r trim_t2
    in case found of
         Nothing -> case g1 blo bhi (singleton kx x) of
                      Tip -> merge kx l' r'
                      (Bin _ _ x' Tip Tip) -> join kx x' l' r'
                      _ -> error "mergeWithKey: Given function only1 does not fulfil required conditions (see documentation)"
         Just x2 -> case f kx x x2 of
                      Nothing -> merge kx l' r'
                      Just x' -> join kx x' l' r'

{-@ trimLookupLo :: (Ord k) 
                 => lo:k 
                 -> bhi:{v: MaybeS k | (isJustS(v) => (lo < fromJustS(v)))} 
                 -> OMap k a 
                 -> (Maybe a, {v: OMap k a | ((isBin(v) => (lo < key(v))) && ((isBin(v) && isJustS(bhi)) => (fromJustS(bhi) > key(v)))) }) @-}

trimLookupLo :: Ord k => k -> MaybeS k -> Map k a -> (Maybe a, Map k a)
trimLookupLo lk NothingS t = greater lk t
  where greater :: Ord k => k -> Map k a -> (Maybe a, Map k a)
        greater lo t'@(Bin _ kx x l r) = case compare lo kx of LT -> (lookup lo l, {-`strictPair`-} t')
                                                               EQ -> (Just x, (case r of {r'@(Bin _ _ _ _ _) -> r' ; r'@Tip -> r'}))
                                                               GT -> greater lo r
        greater _ Tip = (Nothing, Tip)
trimLookupLo lk (JustS hk) t = middle lk hk t
  where middle :: Ord k => k -> k -> Map k a -> (Maybe a, Map k a)
        middle lo hi t'@(Bin _ kx x l r) = case compare lo kx of LT | kx < hi -> (lookup lo l, {- `strictPair` -} t')
                                                                    | otherwise -> middle lo hi l
                                                                 EQ -> (Just x, {-`strictPair`-} lesser lo hi (case r of {r'@(Bin _ _ _ _ _) -> r' ; r'@Tip -> r'}))
                                                                 GT -> middle lo hi r
        middle _ _ Tip = (Nothing, Tip)
 
        lesser :: Ord k => k -> k -> Map k a -> Map k a
        lesser lo hi t'@(Bin _ k _ l _) | k >= hi   = lesser lo hi l
                                        | otherwise = t'
        lesser _ _ t'@Tip = t'
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE trimLookupLo #-}
#endif
