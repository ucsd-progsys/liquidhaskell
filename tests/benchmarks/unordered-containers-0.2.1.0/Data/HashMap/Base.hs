{-# LANGUAGE BangPatterns, CPP, DeriveDataTypeable, MagicHash #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Data.HashMap.Base
    (
      HashMap(..)
    , Leaf(..)

      -- * Construction
    , empty
    , singleton

      -- * Basic interface
    , null
    , size
    , member
    , lookup
    , lookupDefault
    , (!)
    , insert
    , insertWith
    , unsafeInsert
    , delete
    , adjust

      -- * Combine
      -- ** Union
    , union
    , unionWith
    , unions

      -- * Transformations
    , map
    , traverseWithKey

      -- * Difference and intersection
    , difference
    , intersection

      -- * Folds
    , foldl'
    , foldlWithKey'
    , foldr
    , foldrWithKey

      -- * Filter
    , filter
    , filterWithKey

      -- * Conversions
    , keys
    , elems

      -- ** Lists
    , toList
    , fromList
    , fromListWith

      -- Internals used by the strict version
    , Bitmap
    , bitmapIndexedOrFull
    , collision
    , hash
    , mask
    , index
    , bitsPerSubkey
    , fullNodeMask
    , sparseIndex
    , two
    , unionArrayBy
    , update16
    , update16'
    , update16With
    , updateOrConcatWith
    ) where

import Control.Applicative ((<$>), Applicative(pure))
import Control.DeepSeq (NFData(rnf))
import Control.Monad.ST (ST, runST)
import Data.Bits ((.&.), (.|.), complement)
import qualified Data.Foldable as Foldable
import qualified Data.List as L
import Data.Monoid (Monoid(mempty, mappend))
import Data.Traversable (Traversable(..))
import Data.Word (Word)
import Prelude hiding (filter, foldr, lookup, map, null, pred)

import qualified Data.HashMap.Array as A
import qualified Data.Hashable as H
import Data.Hashable (Hashable)
import Data.HashMap.PopCount (popCount)
import Data.HashMap.UnsafeShift (unsafeShiftL, unsafeShiftR)
import Data.Typeable (Typeable)

#if defined(__GLASGOW_HASKELL__)
import GHC.Exts ((==#), build, reallyUnsafePtrEquality#)
#endif

------------------------------------------------------------------------

-- | Convenience function.  Compute a hash value for the given value.
hash :: H.Hashable a => a -> Hash
hash = fromIntegral . H.hash

data Leaf k v = L !k v

instance (NFData k, NFData v) => NFData (Leaf k v) where
    rnf (L k v) = rnf k `seq` rnf v

-- Invariant: The length of the 1st argument to 'Full' is
-- 2^bitsPerSubkey

-- | A map from keys to values.  A map cannot contain duplicate keys;
-- each key can map to at most one value.
data HashMap k v
    = Empty
    | BitmapIndexed !Bitmap !(A.Array (HashMap k v))
    | Leaf !Hash !(Leaf k v)
    | Full !(A.Array (HashMap k v))
    | Collision !Hash !(A.Array (Leaf k v))
      deriving (Typeable)

instance (NFData k, NFData v) => NFData (HashMap k v) where
    rnf Empty                 = ()
    rnf (BitmapIndexed _ ary) = rnf ary
    rnf (Leaf _ l)            = rnf l
    rnf (Full ary)            = rnf ary
    rnf (Collision _ ary)     = rnf ary

instance Functor (HashMap k) where
    fmap = map

instance Foldable.Foldable (HashMap k) where
    foldr f = foldrWithKey (const f)

instance (Eq k, Hashable k) => Monoid (HashMap k v) where
  mempty = empty
  {-# INLINE mempty #-}
  mappend = union
  {-# INLINE mappend #-}

type Hash   = Word
type Bitmap = Word
type Shift  = Int

instance (Show k, Show v) => Show (HashMap k v) where
    show m = "fromList " ++ show (toList m)

instance Traversable (HashMap k) where
    traverse f = traverseWithKey (const f)

-- NOTE: This is just a placeholder.
instance (Eq k, Eq v) => Eq (HashMap k v) where
    a == b = toList a == toList b

------------------------------------------------------------------------
-- * Construction

-- | /O(1)/ Construct an empty map.
empty :: HashMap k v
empty = Empty

-- | /O(1)/ Construct a map with a single element.
singleton :: (Hashable k) => k -> v -> HashMap k v
singleton k v = Leaf (hash k) (L k v)

------------------------------------------------------------------------
-- * Basic interface

-- | /O(1)/ Return 'True' if this map is empty, 'False' otherwise.
null :: HashMap k v -> Bool
null Empty = True
null _   = False

-- | /O(n)/ Return the number of key-value mappings in this map.
size :: HashMap k v -> Int
size t = go t 0
  where
    go Empty                !n = n
    go (Leaf _ _)            n = n + 1
    go (BitmapIndexed _ ary) n = A.foldl' (flip go) n ary
    go (Full ary)            n = A.foldl' (flip go) n ary
    go (Collision _ ary)     n = n + A.length ary

-- | /O(log n)/ Return 'True' if the specified key is present in the
-- map, 'False' otherwise.
member :: (Eq k, Hashable k) => k -> HashMap k a -> Bool
member k m = case lookup k m of
    Nothing -> False
    Just _  -> True
#if __GLASGOW_HASKELL__ >= 700
{-# INLINEABLE member #-}
#endif

-- | /O(log n)/ Return the value to which the specified key is mapped,
-- or 'Nothing' if this map contains no mapping for the key.
lookup :: (Eq k, Hashable k) => k -> HashMap k v -> Maybe v
lookup k0 = go h0 k0 0
  where
    h0 = hash k0
    go !_ !_ !_ Empty = Nothing
    go h k _ (Leaf hx (L kx x))
        | h == hx && k == kx = Just x  -- TODO: Split test in two
        | otherwise          = Nothing
    go h k s (BitmapIndexed b v)
        | b .&. m == 0 = Nothing
        | otherwise    = go h k (s+bitsPerSubkey) (A.index v (sparseIndex b m))
      where m = mask h s
    go h k s (Full v) = go h k (s+bitsPerSubkey) (A.index v (index h s))
    go h k _ (Collision hx v)
        | h == hx   = lookupInArray k v
        | otherwise = Nothing
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE lookup #-}
#endif

-- | /O(log n)/ Return the value to which the specified key is mapped,
-- or the default value if this map contains no mapping for the key.
lookupDefault :: (Eq k, Hashable k)
              => v          -- ^ Default value to return.
              -> k -> HashMap k v -> v
lookupDefault def k t = case lookup k t of
    Just v -> v
    _      -> def
{-# INLINE lookupDefault #-}

-- | /O(log n)/ Return the value to which the specified key is mapped.
-- Calls 'error' if this map contains no mapping for the key.
(!) :: (Eq k, Hashable k) => HashMap k v -> k -> v
(!) m k = case lookup k m of
    Just v  -> v
    Nothing -> error "Data.HashMap.Base.(!): key not found"
{-# INLINABLE (!) #-}

infixl 9 !

-- | Create a 'Collision' value with two 'Leaf' values.
collision :: Hash -> Leaf k v -> Leaf k v -> HashMap k v
collision h e1 e2 =
    let v = A.run $ do mary <- A.new 2 e1
                       A.write mary 1 e2
                       return mary
    in Collision h v
{-# INLINE collision #-}

-- | Create a 'BitmapIndexed' or 'Full' node.
bitmapIndexedOrFull :: Bitmap -> A.Array (HashMap k v) -> HashMap k v
bitmapIndexedOrFull b ary
    | b == fullNodeMask = Full ary
    | otherwise         = BitmapIndexed b ary
{-# INLINE bitmapIndexedOrFull #-}

-- | /O(log n)/ Associate the specified value with the specified
-- key in this map.  If this map previously contained a mapping for
-- the key, the old value is replaced.
insert :: (Eq k, Hashable k) => k -> v -> HashMap k v -> HashMap k v
insert k0 v0 m0 = runST (go h0 k0 v0 0 m0)
  where
    h0 = hash k0
    go !h !k x !_ Empty = return $! Leaf h (L k x)
    go h k x s t@(Leaf hy l@(L ky y))
        | hy == h = if ky == k
                    then if x `ptrEq` y
                         then return t
                         else return $! Leaf h (L k x)
                    else return $! collision h l (L k x)
        | otherwise = two s h k x hy ky y
    go h k x s t@(BitmapIndexed b ary)
        | b .&. m == 0 = do
            !ary' <- A.insert' ary i $! Leaf h (L k x)
            return $! bitmapIndexedOrFull (b .|. m) ary'
        | otherwise = do
            st <- A.index_ ary i
            !st' <- go h k x (s+bitsPerSubkey) st
            if st' `ptrEq` st
                then return t
                else do
                    ary' <- A.update' ary i st'
                    return $! BitmapIndexed b ary'
      where m = mask h s
            i = sparseIndex b m
    go h k x s t@(Full ary) = do
        st <- A.index_ ary i
        !st' <- go h k x (s+bitsPerSubkey) st
        if st' `ptrEq` st
            then return t
            else do
                ary' <- update16' ary i st'
                return $! Full ary'
      where i = index h s
    go h k x s t@(Collision hy v)
        | h == hy   = return $! Collision h (updateOrSnocWith const k x v)
        | otherwise = go h k x s $ BitmapIndexed (mask hy s) (A.singleton t)
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE insert #-}
#endif

-- | In-place update version of insert
unsafeInsert :: (Eq k, Hashable k) => k -> v -> HashMap k v -> HashMap k v
unsafeInsert k0 v0 m0 = runST (go h0 k0 v0 0 m0)
  where
    h0 = hash k0
    go !h !k x !_ Empty = return $! Leaf h (L k x)
    go h k x s t@(Leaf hy l@(L ky y))
        | hy == h = if ky == k
                    then if x `ptrEq` y
                         then return t
                         else return $! Leaf h (L k x)
                    else return $! collision h l (L k x)
        | otherwise = two s h k x hy ky y
    go h k x s t@(BitmapIndexed b ary)
        | b .&. m == 0 = do
            ary' <- A.insert' ary i $! Leaf h (L k x)
            return $! bitmapIndexedOrFull (b .|. m) ary'
        | otherwise = do
            st <- A.index_ ary i
            st' <- go h k x (s+bitsPerSubkey) st
            A.unsafeUpdate' ary i st'
            return t
      where m = mask h s
            i = sparseIndex b m
    go h k x s t@(Full ary) = do
        st <- A.index_ ary i
        st' <- go h k x (s+bitsPerSubkey) st
        A.unsafeUpdate' ary i st'
        return t
      where i = index h s
    go h k x s t@(Collision hy v)
        | h == hy   = return $! Collision h (updateOrSnocWith const k x v)
        | otherwise = go h k x s $ BitmapIndexed (mask hy s) (A.singleton t)
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE unsafeInsert #-}
#endif

-- | Create a map from two key-value pairs which hashes don't collide.
two :: Shift -> Hash -> k -> v -> Hash -> k -> v -> ST s (HashMap k v)
two = go
  where
    go s h1 k1 v1 h2 k2 v2
        | bp1 == bp2 = do
            st <- go (s+bitsPerSubkey) h1 k1 v1 h2 k2 v2 
            ary <- A.singleton' st
            return $! BitmapIndexed bp1 ary
        | otherwise  = do
            mary <- A.new 2 $ Leaf h1 (L k1 v1)
            A.write mary idx2 $ Leaf h2 (L k2 v2)
            ary <- A.unsafeFreeze mary
            return $! BitmapIndexed (bp1 .|. bp2) ary
      where
        bp1  = mask h1 s
        bp2  = mask h2 s
        idx2 | index h1 s < index h2 s = 1
             | otherwise               = 0
{-# INLINE two #-}

-- | /O(log n)/ Associate the value with the key in this map.  If
-- this map previously contained a mapping for the key, the old value
-- is replaced by the result of applying the given function to the new
-- and old value.  Example:
--
-- > insertWith f k v map
-- >   where f new old = new + old
insertWith :: (Eq k, Hashable k) => (v -> v -> v) -> k -> v -> HashMap k v
            -> HashMap k v
insertWith f k0 v0 m0 = runST (go h0 k0 v0 0 m0)
  where
    h0 = hash k0
    go !h !k x !_ Empty = return $! Leaf h (L k x)
    go h k x s (Leaf hy l@(L ky y))
        | hy == h = if ky == k
                    then return $! Leaf h (L k (f x y))
                    else return $! collision h l (L k x)
        | otherwise = two s h k x hy ky y
    go h k x s (BitmapIndexed b ary)
        | b .&. m == 0 = do
            ary' <- A.insert' ary i $! Leaf h (L k x)
            return $! bitmapIndexedOrFull (b .|. m) ary'
        | otherwise = do
            st <- A.index_ ary i
            st' <- go h k x (s+bitsPerSubkey) st
            ary' <- A.update' ary i st'
            return $! BitmapIndexed b ary'
      where m = mask h s
            i = sparseIndex b m
    go h k x s (Full ary) = do
        st <- A.index_ ary i
        st' <- go h k x (s+bitsPerSubkey) st
        ary' <- update16' ary i st'
        return $! Full ary'
      where i = index h s
    go h k x s t@(Collision hy v)
        | h == hy   = return $! Collision h (updateOrSnocWith f k x v)
        | otherwise = go h k x s $ BitmapIndexed (mask hy s) (A.singleton t)
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE insertWith #-}
#endif

-- | In-place update version of insertWith
unsafeInsertWith :: (Eq k, Hashable k) => (v -> v -> v) -> k -> v -> HashMap k v
                 -> HashMap k v
unsafeInsertWith f k0 v0 m0 = runST (go h0 k0 v0 0 m0)
  where
    h0 = hash k0
    go !h !k x !_ Empty = return $! Leaf h (L k x)
    go h k x s (Leaf hy l@(L ky y))
        | hy == h = if ky == k
                    then return $! Leaf h (L k (f x y))
                    else return $! collision h l (L k x)
        | otherwise = two s h k x hy ky y
    go h k x s t@(BitmapIndexed b ary)
        | b .&. m == 0 = do
            ary' <- A.insert' ary i $! Leaf h (L k x)
            return $! bitmapIndexedOrFull (b .|. m) ary'
        | otherwise = do
            st <- A.index_ ary i
            st' <- go h k x (s+bitsPerSubkey) st
            A.unsafeUpdate' ary i st'
            return t
      where m = mask h s
            i = sparseIndex b m
    go h k x s t@(Full ary) = do
        st <- A.index_ ary i
        st' <- go h k x (s+bitsPerSubkey) st
        A.unsafeUpdate' ary i st'
        return t
      where i = index h s
    go h k x s t@(Collision hy v)
        | h == hy   = return $! Collision h (updateOrSnocWith f k x v)
        | otherwise = go h k x s $ BitmapIndexed (mask hy s) (A.singleton t)
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE unsafeInsertWith #-}
#endif

-- | /O(log n)/ Remove the mapping for the specified key from this map
-- if present.
delete :: (Eq k, Hashable k) => k -> HashMap k v -> HashMap k v
delete k0 m0 = runST (go h0 k0 0 m0)
  where
    h0 = hash k0
    go !_ !_ !_ Empty = return Empty
    go h k _ t@(Leaf hy (L ky _))
        | hy == h && ky == k = return Empty
        | otherwise          = return t
    go h k s t@(BitmapIndexed b ary)
        | b .&. m == 0 = return t
        | otherwise = do
            let !st = A.index ary i
            !st' <- go h k (s+bitsPerSubkey) st
            if st' `ptrEq` st
                then return t
                else case st' of
                Empty | A.length ary == 1 -> return Empty
                      | otherwise -> do
                          ary' <- A.delete' ary i
                          return $! BitmapIndexed (b .&. complement m) ary'
                _ -> do
                    ary' <- A.update' ary i st'
                    return $! BitmapIndexed b ary'
      where m = mask h s
            i = sparseIndex b m
    go h k s t@(Full ary) = do
        let !st = A.index ary i
        !st' <- go h k (s+bitsPerSubkey) st
        if st' `ptrEq` st
            then return t
            else case st' of
            Empty -> do
                ary' <- A.delete' ary i
                let bm = fullNodeMask .&. complement (1 `unsafeShiftL` i)
                return $! BitmapIndexed bm ary'
            _ -> do
                ary' <- A.update' ary i st'
                return $! Full ary'
      where i = index h s
    go h k _ t@(Collision hy v)
        | h == hy = case indexOf k v of
            Just i
                | A.length v == 2 ->
                    if i == 0
                    then return $! Leaf h (A.index v 1)
                    else return $! Leaf h (A.index v 0)
                | otherwise -> return $! Collision h (A.delete v i)
            Nothing -> return t
        | otherwise = return t
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE delete #-}
#endif

-- | /O(log n)/ Adjust the value tied to a given key in this map only
-- if it is present. Otherwise, leave the map alone.
adjust :: (Eq k, Hashable k) => (v -> v) -> k -> HashMap k v -> HashMap k v
adjust f k0 = go h0 k0 0
  where
    h0 = hash k0
    go !_ !_ !_ Empty = Empty
    go h k _ t@(Leaf hy (L ky y))
        | hy == h && ky == k = Leaf h (L k (f y))
        | otherwise          = t
    go h k s t@(BitmapIndexed b ary)
        | b .&. m == 0 = t
        | otherwise = let st   = A.index ary i
                          st'  = go h k (s+bitsPerSubkey) st
                          ary' = A.update ary i $! st'
                      in BitmapIndexed b ary'
      where m = mask h s
            i = sparseIndex b m
    go h k s (Full ary) =
        let i    = index h s
            st   = A.index ary i
            st'  = go h k (s+bitsPerSubkey) st
            ary' = update16 ary i $! st'
        in Full ary'
    go h k _ t@(Collision hy v)
        | h == hy   = Collision h (updateWith f k v)
        | otherwise = t
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE adjust #-}
#endif

------------------------------------------------------------------------
-- * Combine

-- | /O(n+m)/ The union of two maps. If a key occurs in both maps, the
-- mapping from the first will be the mapping in the result.
union :: (Eq k, Hashable k) => HashMap k v -> HashMap k v -> HashMap k v
union = unionWith const
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE union #-}
#endif

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the
-- result.
unionWith :: (Eq k, Hashable k) => (v -> v -> v) -> HashMap k v -> HashMap k v
          -> HashMap k v
unionWith f = go 0
  where
    -- empty vs. anything
    go !_ t1 Empty = t1
    go _ Empty t2 = t2
    -- leaf vs. leaf
    go s t1@(Leaf h1 l1@(L k1 v1)) t2@(Leaf h2 l2@(L k2 v2))
        | h1 == h2  = if k1 == k2
                      then Leaf h1 (L k1 (f v1 v2))
                      else collision h1 l1 l2
        | otherwise = goDifferentHash s h1 h2 t1 t2
    go s t1@(Leaf h1 (L k1 v1)) t2@(Collision h2 ls2)
        | h1 == h2  = Collision h1 (updateOrSnocWith f k1 v1 ls2)
        | otherwise = goDifferentHash s h1 h2 t1 t2
    go s t1@(Collision h1 ls1) t2@(Leaf h2 (L k2 v2))
        | h1 == h2  = Collision h1 (updateOrSnocWith (flip f) k2 v2 ls1)
        | otherwise = goDifferentHash s h1 h2 t1 t2
    go s t1@(Collision h1 ls1) t2@(Collision h2 ls2)
        | h1 == h2  = Collision h1 (updateOrConcatWith f ls1 ls2)
        | otherwise = goDifferentHash s h1 h2 t1 t2
    -- branch vs. branch
    go s (BitmapIndexed b1 ary1) (BitmapIndexed b2 ary2) =
        let b'   = b1 .|. b2
            ary' = unionArrayBy (go (s+bitsPerSubkey)) b1 b2 ary1 ary2
        in bitmapIndexedOrFull b' ary'
    go s (BitmapIndexed b1 ary1) (Full ary2) =
        let ary' = unionArrayBy (go (s+bitsPerSubkey)) b1 fullNodeMask ary1 ary2
        in Full ary'
    go s (Full ary1) (BitmapIndexed b2 ary2) =
        let ary' = unionArrayBy (go (s+bitsPerSubkey)) fullNodeMask b2 ary1 ary2
        in Full ary'
    go s (Full ary1) (Full ary2) =
        let ary' = unionArrayBy (go (s+bitsPerSubkey)) fullNodeMask fullNodeMask
                   ary1 ary2
        in Full ary'
    -- leaf vs. branch
    go s (BitmapIndexed b1 ary1) t2
        | b1 .&. m2 == 0 = let ary' = A.insert ary1 i t2
                               b'   = b1 .|. m2
                           in bitmapIndexedOrFull b' ary'
        | otherwise      = let ary' = A.updateWith ary1 i $ \st1 ->
                                   go (s+bitsPerSubkey) st1 t2
                           in BitmapIndexed b1 ary'
        where
          h2 = leafHashCode t2
          m2 = mask h2 s
          i = sparseIndex b1 m2
    go s t1 (BitmapIndexed b2 ary2)
        | b2 .&. m1 == 0 = let ary' = A.insert ary2 i $! t1
                               b'   = b2 .|. m1
                           in bitmapIndexedOrFull b' ary'
        | otherwise      = let ary' = A.updateWith ary2 i $ \st2 ->
                                   go (s+bitsPerSubkey) t1 st2
                           in BitmapIndexed b2 ary'
      where
        h1 = leafHashCode t1
        m1 = mask h1 s
        i = sparseIndex b2 m1
    go s (Full ary1) t2 =
        let h2   = leafHashCode t2
            i    = index h2 s
            ary' = update16With ary1 i $ \st1 -> go (s+bitsPerSubkey) st1 t2
        in Full ary'
    go s t1 (Full ary2) =
        let h1   = leafHashCode t1
            i    = index h1 s
            ary' = update16With ary2 i $ \st2 -> go (s+bitsPerSubkey) t1 st2
        in Full ary'

    leafHashCode (Leaf h _) = h
    leafHashCode (Collision h _) = h
    leafHashCode _ = error "leafHashCode"

    goDifferentHash s h1 h2 t1 t2
        | m1 == m2  = BitmapIndexed m1 (A.singleton $! go (s+bitsPerSubkey) t1 t2)
        | m1 <  m2  = BitmapIndexed (m1 .|. m2) (A.pair t1 t2)
        | otherwise = BitmapIndexed (m1 .|. m2) (A.pair t2 t1)
      where
        m1 = mask h1 s
        m2 = mask h2 s
{-# INLINE unionWith #-}

-- | Strict in the result of @f@.
unionArrayBy :: (a -> a -> a) -> Bitmap -> Bitmap -> A.Array a -> A.Array a
             -> A.Array a
unionArrayBy f b1 b2 ary1 ary2 = A.run $ do
    let b' = b1 .|. b2
    mary <- A.new_ (popCount b')
    -- iterate over nonzero bits of b1 .|. b2
    -- it would be nice if we could shift m by more than 1 each time
    let hasBit b m = b .&. m /= 0
        go !i !i1 !i2 !m
            | m > b'                     = return ()
            | hasBit b1 m && hasBit b2 m = do
                A.write mary i $! f (A.index ary1 i1) (A.index ary2 i2)
                go (i+1) (i1+1) (i2+1) (m `unsafeShiftL` 1)
            | hasBit b1 m                = do
                A.write mary i =<< A.index_ ary1 i1
                go (i+1) (i1+1) (i2  ) (m `unsafeShiftL` 1)
            | hasBit b2 m                = do
                A.write mary i =<< A.index_ ary2 i2
                go (i+1) (i1  ) (i2+1) (m `unsafeShiftL` 1)
            | otherwise                  = go i i1 i2 (m `unsafeShiftL` 1)
    go 0 0 0 1
    return mary
    -- TODO: For the case where b1 .&. b2 == b1, i.e. when one is a
    -- subset of the other, we could use a slightly simpler algorithm,
    -- where we copy one array, and then update.
{-# INLINE unionArrayBy #-}

-- TODO: Figure out the time complexity of 'unions'.

-- | Construct a set containing all elements from a list of sets.
unions :: (Eq k, Hashable k) => [HashMap k v] -> HashMap k v
unions = L.foldl' union empty
{-# INLINE unions #-}

------------------------------------------------------------------------
-- * Transformations

-- | /O(n)/ Transform this map by applying a function to every value.
map :: (v1 -> v2) -> HashMap k v1 -> HashMap k v2
map f = go
  where
    go Empty = Empty
    go (Leaf h (L k v)) = Leaf h $ L k (f v)
    go (BitmapIndexed b ary) = BitmapIndexed b $ A.map' go ary
    go (Full ary) = Full $ A.map' go ary
    go (Collision h ary) = Collision h $
                           A.map' (\ (L k v) -> L k (f v)) ary
{-# INLINE map #-}

-- | /O(n)/ Transform this map by accumulating an Applicative result
-- from every value.
traverseWithKey :: Applicative f => (k -> v1 -> f v2) -> HashMap k v1
                -> f (HashMap k v2)
traverseWithKey f = go
  where
    go Empty                 = pure Empty
    go (Leaf h (L k v))      = Leaf h . L k <$> f k v
    go (BitmapIndexed b ary) = BitmapIndexed b <$> A.traverse go ary
    go (Full ary)            = Full <$> A.traverse go ary
    go (Collision h ary)     =
        Collision h <$> A.traverse (\ (L k v) -> L k <$> f k v) ary
{-# INLINE traverseWithKey #-}

------------------------------------------------------------------------
-- * Difference and intersection

-- | /O(n+m)/ Difference of two maps. Return elements of the first map
-- not existing in the second.
difference :: (Eq k, Hashable k) => HashMap k v -> HashMap k w -> HashMap k v
difference a b = foldlWithKey' go empty a
  where
    go m k v = case lookup k b of
                 Nothing -> insert k v m
                 _       -> m
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE difference #-}
#endif

-- | /O(n+m)/ Intersection of two maps. Return elements of the first
-- map for keys existing in the second.
intersection :: (Eq k, Hashable k) => HashMap k v -> HashMap k w -> HashMap k v
intersection a b = foldlWithKey' go empty a
  where
    go m k v = case lookup k b of
                 Just _ -> insert k v m
                 _      -> m
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE intersection #-}
#endif

------------------------------------------------------------------------
-- * Folds

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- left-identity of the operator).  Each application of the operator
-- is evaluated before before using the result in the next
-- application.  This function is strict in the starting value.
foldl' :: (a -> v -> a) -> a -> HashMap k v -> a
foldl' f = foldlWithKey' (\ z _ v -> f z v)
{-# INLINE foldl' #-}

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- left-identity of the operator).  Each application of the operator
-- is evaluated before before using the result in the next
-- application.  This function is strict in the starting value.
foldlWithKey' :: (a -> k -> v -> a) -> a -> HashMap k v -> a
foldlWithKey' f = go
  where
    go !z Empty                = z
    go z (Leaf _ (L k v))      = f z k v
    go z (BitmapIndexed _ ary) = A.foldl' go z ary
    go z (Full ary)            = A.foldl' go z ary
    go z (Collision _ ary)     = A.foldl' (\ z' (L k v) -> f z' k v) z ary
{-# INLINE foldlWithKey' #-}

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- right-identity of the operator).
foldr :: (v -> a -> a) -> a -> HashMap k v -> a
foldr f = foldrWithKey (const f)
{-# INLINE foldr #-}

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- right-identity of the operator).
foldrWithKey :: (k -> v -> a -> a) -> a -> HashMap k v -> a
foldrWithKey f = go
  where
    go z Empty                 = z
    go z (Leaf _ (L k v))      = f k v z
    go z (BitmapIndexed _ ary) = A.foldr (flip go) z ary
    go z (Full ary)            = A.foldr (flip go) z ary
    go z (Collision _ ary)     = A.foldr (\ (L k v) z' -> f k v z') z ary
{-# INLINE foldrWithKey #-}

------------------------------------------------------------------------
-- * Filter

-- | Create a new array of the @n@ first elements of @mary@.
trim :: A.MArray s a -> Int -> ST s (A.Array a)
trim mary n = do
    mary2 <- A.new_ n
    A.copyM mary 0 mary2 0 n
    A.unsafeFreeze mary2
{-# INLINE trim #-}

-- | /O(n)/ Filter this map by retaining only elements satisfying a
-- predicate.
filterWithKey :: (k -> v -> Bool) -> HashMap k v -> HashMap k v
filterWithKey pred = go
  where
    go Empty = Empty
    go t@(Leaf _ (L k v))
        | pred k v  = t
        | otherwise = Empty
    go (BitmapIndexed b ary) = filterA ary b
    go (Full ary) = filterA ary fullNodeMask
    go (Collision h ary) = filterC ary h

    filterA ary0 b0 =
        let !n = A.length ary0
        in runST $ do
            mary <- A.new_ n
            step ary0 mary b0 0 0 1 n
      where
        step !ary !mary !b i !j !bi n
            | i >= n = case j of
                0 -> return Empty
                _ -> do
                    ary2 <- trim mary j
                    return $! if j == maxChildren
                              then Full ary2
                              else BitmapIndexed b ary2
            | bi .&. b == 0 = step ary mary b i j (bi `unsafeShiftL` 1) n
            | otherwise = case go (A.index ary i) of
                Empty -> step ary mary (b .&. complement bi) (i+1) j
                         (bi `unsafeShiftL` 1) n
                t     -> do A.write mary j t
                            step ary mary b (i+1) (j+1) (bi `unsafeShiftL` 1) n

    filterC ary0 h =
        let !n = A.length ary0
        in runST $ do
            mary <- A.new_ n
            step ary0 mary 0 0 n
      where
        step !ary !mary i !j n
            | i >= n    = case j of
                0 -> return Empty
                1 -> do l <- A.read mary 0
                        return $! Leaf h l
                _ | i == j -> do ary2 <- A.unsafeFreeze mary
                                 return $! Collision h ary2
                  | otherwise -> do ary2 <- trim mary j
                                    return $! Collision h ary2
            | pred k v  = A.write mary j el >> step ary mary (i+1) (j+1) n
            | otherwise = step ary mary (i+1) j n
          where el@(L k v) = A.index ary i
{-# INLINE filterWithKey #-}

-- | /O(n)/ Filter this map by retaining only elements which values
-- satisfy a predicate.
filter :: (v -> Bool) -> HashMap k v -> HashMap k v
filter p = filterWithKey (\_ v -> p v)
{-# INLINE filter #-}

------------------------------------------------------------------------
-- * Conversions

-- TODO: Improve fusion rules by modelled them after the Prelude ones
-- on lists.

-- | /O(n)/ Return a list of this map's keys.  The list is produced
-- lazily.
keys :: HashMap k v -> [k]
keys = L.map fst . toList
{-# INLINE keys #-}

-- | /O(n)/ Return a list of this map's values.  The list is produced
-- lazily.
elems :: HashMap k v -> [v]
elems = L.map snd . toList
{-# INLINE elems #-}

------------------------------------------------------------------------
-- ** Lists

-- | /O(n)/ Return a list of this map's elements.  The list is
-- produced lazily.
toList :: HashMap k v -> [(k, v)]
#if defined(__GLASGOW_HASKELL__)
toList t = build (\ c z -> foldrWithKey (curry c) z t)
#else
toList = foldrWithKey (\ k v xs -> (k, v) : xs) []
#endif
{-# INLINE toList #-}

-- | /O(n)/ Construct a map with the supplied mappings.  If the list
-- contains duplicate mappings, the later mappings take precedence.
fromList :: (Eq k, Hashable k) => [(k, v)] -> HashMap k v
fromList = L.foldl' (\ m (k, v) -> unsafeInsert k v m) empty
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE fromList #-}
#endif

-- | /O(n*log n)/ Construct a map from a list of elements.  Uses
-- the provided function to merge duplicate entries.
fromListWith :: (Eq k, Hashable k) => (v -> v -> v) -> [(k, v)] -> HashMap k v
fromListWith f = L.foldl' (\ m (k, v) -> unsafeInsertWith f k v m) empty
#if __GLASGOW_HASKELL__ >= 700
{-# INLINE fromListWith #-}
#endif

------------------------------------------------------------------------
-- Array operations

-- | /O(n)/ Lookup the value associated with the given key in this
-- array.  Returns 'Nothing' if the key wasn't found.
lookupInArray :: Eq k => k -> A.Array (Leaf k v) -> Maybe v
lookupInArray k0 ary0 = go k0 ary0 0 (A.length ary0)
  where
    go !k !ary !i !n
        | i >= n    = Nothing
        | otherwise = case A.index ary i of
            (L kx v)
                | k == kx   -> Just v
                | otherwise -> go k ary (i+1) n
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE lookupInArray #-}
#endif

-- | /O(n)/ Lookup the value associated with the given key in this
-- array.  Returns 'Nothing' if the key wasn't found.
indexOf :: Eq k => k -> A.Array (Leaf k v) -> Maybe Int
indexOf k0 ary0 = go k0 ary0 0 (A.length ary0)
  where
    go !k !ary !i !n
        | i >= n    = Nothing
        | otherwise = case A.index ary i of
            (L kx _)
                | k == kx   -> Just i
                | otherwise -> go k ary (i+1) n
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE indexOf #-}
#endif

updateWith :: Eq k => (v -> v) -> k -> A.Array (Leaf k v) -> A.Array (Leaf k v)
updateWith f k0 ary0 = go k0 ary0 0 (A.length ary0)
  where
    go !k !ary !i !n
        | i >= n    = ary
        | otherwise = case A.index ary i of
            (L kx y) | k == kx   -> A.update ary i (L k (f y))
                     | otherwise -> go k ary (i+1) n
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE updateWith #-}
#endif

updateOrSnocWith :: Eq k => (v -> v -> v) -> k -> v -> A.Array (Leaf k v)
                 -> A.Array (Leaf k v)
updateOrSnocWith f k0 v0 ary0 = go k0 v0 ary0 0 (A.length ary0)
  where
    go !k v !ary !i !n
        | i >= n = A.run $ do
            -- Not found, append to the end.
            mary <- A.new_ (n + 1)
            A.copy ary 0 mary 0 n
            A.write mary n (L k v)
            return mary
        | otherwise = case A.index ary i of
            (L kx y) | k == kx   -> A.update ary i (L k (f v y))
                     | otherwise -> go k v ary (i+1) n
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE updateOrSnocWith #-}
#endif

updateOrConcatWith :: Eq k => (v -> v -> v) -> A.Array (Leaf k v) -> A.Array (Leaf k v) -> A.Array (Leaf k v)
updateOrConcatWith f ary1 ary2 = A.run $ do
    -- first: look up the position of each element of ary2 in ary1
    let indices = A.map (\(L k _) -> indexOf k ary1) ary2
    -- that tells us how large the overlap is:
    -- count number of Nothing constructors
    let nOnly2 = A.foldl' (\n -> maybe (n+1) (const n)) 0 indices
    let n1 = A.length ary1
    let n2 = A.length ary2
    -- copy over all elements from ary1
    mary <- A.new_ (n1 + nOnly2)
    A.copy ary1 0 mary 0 n1
    -- append or update all elements from ary2
    let go !iEnd !i2
          | i2 >= n2 = return ()
          | otherwise = case A.index indices i2 of
               Just i1 -> do -- key occurs in both arrays, store combination in position i1
                             L k v1 <- A.index_ ary1 i1
                             L _ v2 <- A.index_ ary2 i2
                             A.write mary i1 (L k (f v1 v2))
                             go iEnd (i2+1)
               Nothing -> do -- key is only in ary2, append to end
                             A.write mary iEnd =<< A.index_ ary2 i2
                             go (iEnd+1) (i2+1)
    go n1 0
    return mary
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE updateOrConcatWith #-}
#endif

------------------------------------------------------------------------
-- Manually unrolled loops

-- | /O(n)/ Update the element at the given position in this array.
update16 :: A.Array e -> Int -> e -> A.Array e
update16 ary idx b = runST (update16' ary idx b)
{-# INLINE update16 #-}

-- | /O(n)/ Update the element at the given position in this array.
update16' :: A.Array e -> Int -> e -> ST s (A.Array e)
update16' ary idx b = do
    mary <- clone16 ary
    A.write mary idx b
    A.unsafeFreeze mary
{-# INLINE update16' #-}

-- | /O(n)/ Update the element at the given position in this array, by applying a function to it.
update16With :: A.Array e -> Int -> (e -> e) -> A.Array e
update16With ary idx f = update16 ary idx $! f (A.index ary idx)
{-# INLINE update16With #-}

-- | Unsafely clone an array of 16 elements.  The length of the input
-- array is not checked.
clone16 :: A.Array e -> ST s (A.MArray s e)
clone16 ary =
#if __GLASGOW_HASKELL__ >= 702
    A.thaw ary 0 16
#else
    do mary <- A.new_ 16
       A.index_ ary 0 >>= A.write mary 0
       A.index_ ary 1 >>= A.write mary 1
       A.index_ ary 2 >>= A.write mary 2
       A.index_ ary 3 >>= A.write mary 3
       A.index_ ary 4 >>= A.write mary 4
       A.index_ ary 5 >>= A.write mary 5
       A.index_ ary 6 >>= A.write mary 6
       A.index_ ary 7 >>= A.write mary 7
       A.index_ ary 8 >>= A.write mary 8
       A.index_ ary 9 >>= A.write mary 9
       A.index_ ary 10 >>= A.write mary 10
       A.index_ ary 11 >>= A.write mary 11
       A.index_ ary 12 >>= A.write mary 12
       A.index_ ary 13 >>= A.write mary 13
       A.index_ ary 14 >>= A.write mary 14
       A.index_ ary 15 >>= A.write mary 15
       return mary
#endif

------------------------------------------------------------------------
-- Bit twiddling

bitsPerSubkey :: Int
bitsPerSubkey = 4

maxChildren :: Int
maxChildren = fromIntegral $ 1 `unsafeShiftL` bitsPerSubkey

subkeyMask :: Bitmap
subkeyMask = 1 `unsafeShiftL` bitsPerSubkey - 1

sparseIndex :: Bitmap -> Bitmap -> Int
sparseIndex b m = popCount (b .&. (m - 1))

mask :: Word -> Shift -> Bitmap
mask w s = 1 `unsafeShiftL` index w s
{-# INLINE mask #-}

-- | Mask out the 'bitsPerSubkey' bits used for indexing at this level
-- of the tree.
index :: Hash -> Shift -> Int
index w s = fromIntegral $ (unsafeShiftR w s) .&. subkeyMask
{-# INLINE index #-}

-- | A bitmask with the 'bitsPerSubkey' least significant bits set.
fullNodeMask :: Bitmap
fullNodeMask = complement (complement 0 `unsafeShiftL` maxChildren)
{-# INLINE fullNodeMask #-}

-- | Check if two the two arguments are the same value.  N.B. This
-- function might give false negatives (due to GC moving objects.)
ptrEq :: a -> a -> Bool
#if defined(__GLASGOW_HASKELL__)
ptrEq x y = reallyUnsafePtrEquality# x y ==# 1#
#else
ptrEq _ _ = False
#endif
{-# INLINE ptrEq #-}
