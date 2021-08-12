{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.ShareMap
  ( ShareMap
  , empty
  , toHashMap
  , insertWith
  , map
  , mergeKeysWith
  ) where

import           Data.Hashable (Hashable)
import           Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import           Data.Maybe (fromMaybe)
import           Prelude hiding (map)

-- | A HashMap that can share the values of some entries
--
-- If two keys @k1@ and @k2@ are mapped to single @v@, updating
-- the entry for @k1@ also updates the entry for @k2@ and viceversa.
--
-- The user of the map is responsible for indicating which keys are
-- going to share their values.
--
-- Keys can be updated with 'shareMapInsertWith' and 'mergeKeysWith'.
data ShareMap k v = ShareMap
  { -- | @(k, v)@ pairs in the map.
    --
    -- Contains at least an entry for each key in the values of
    -- of 'shareMap'.
    unsharedMap :: HashMap (InternalKey k) v
  , -- | If @k1@ is mapped to @k2@, then both keys are considered
    -- associated to the value of @k2@ in 'unsharedMap'.
    --
    -- Contains an entry for each key in the 'ShareMap'.
    shareMap :: ReversibleMap k (InternalKey k)
  }
  deriving Show

-- | This are the only keys that can be used in internal maps
newtype InternalKey k = InternalKey k
  deriving (Eq, Hashable)

instance Show k => Show (InternalKey k) where
  show (InternalKey k) = show k

empty :: ShareMap k v
empty = ShareMap HashMap.empty emptyReversibleMap

toHashMap :: (Hashable k, Eq k) => ShareMap k v -> HashMap k v
toHashMap sm =
  HashMap.foldlWithKey' expand HashMap.empty (directMap $ shareMap sm)
  where
    expand m k k' =
      maybe m (\v -> HashMap.insert k v m) (HashMap.lookup k' $ unsharedMap sm)

-- | @insertWith f k v m@ is the map @m@ plus key @k@ being associated to
-- value @v@.
--
-- If @k@ is present in @m@, then @k@ and any other key sharing its value
-- will be associated to @f v (m ! k)@.
--
insertWith
  :: (Hashable k, Eq k)
  => (v -> v -> v)
  -> k
  -> v
  -> ShareMap k v
  -> ShareMap k v
insertWith f k v sm =
  case HashMap.lookup k $ directMap $ shareMap sm of
    Just k' -> sm
      { unsharedMap = HashMap.insertWith f k' v (unsharedMap sm)
      }
    Nothing -> ShareMap
      { unsharedMap = HashMap.insertWith f (InternalKey k) v (unsharedMap sm)
      , shareMap = insertReversibleMap k (InternalKey k) (shareMap sm)
      }

-- | @mergeKeysWith f k0 k1 m@ updates the @k0@ value to @f (m ! k0) (m ! k1)@
-- and @k1@ shares the value with @k0@.
--
-- If @k0@ and @k1@ are already sharing their values in @m@, or both keys are
-- missing, this operation returns @m@ unmodified.
--
-- If only one of the keys is present, the other key is associated with the
-- existing value.
mergeKeysWith
  :: (Hashable k, Eq k)
  => (v -> v -> v)
  -> k
  -> k
  -> ShareMap k v
  -> ShareMap k v
mergeKeysWith f k0 k1 sm | k0 /= k1 =
  case lookupReversibleMap k1 (shareMap sm) of
    Just k1' | InternalKey k0 /= k1' -> case HashMap.lookup k1' (unsharedMap sm) of
      Just v1 -> case lookupReversibleMap k0 (shareMap sm) of
        Just k0' | k0' /= k1' ->
          ShareMap
            { unsharedMap = HashMap.insertWith (flip f) k0' v1 (unsharedMap sm)
            , shareMap = -- Any values pointing to k1 are redirected to k0':
                HashSet.foldl' (\m k -> insertReversibleMap k k0' m) (shareMap sm) $
                reverseLookup k1' $ shareMap sm
            }
        Nothing ->
          sm { shareMap = insertReversibleMap k0 k1' (shareMap sm) }
        _ ->
          sm
      Nothing -> error "mergeKeysWith: broken invariant: unexpected missing key in unsharedMap"
    Nothing ->
      case HashMap.lookup k0 (directMap $ shareMap sm) of
        Just k0' ->
          sm { shareMap = insertReversibleMap k1 k0' (shareMap sm) }
        Nothing ->
          sm
    _ ->
      sm
mergeKeysWith _ _ _ sm = sm

map :: (a -> b) -> ShareMap k a -> ShareMap k b
map f sm = sm { unsharedMap = HashMap.map f (unsharedMap sm) }

-- | A map with an efficient 'reverseLookup'
data ReversibleMap k v = ReversibleMap
  { directMap :: HashMap k v
  , -- |
    -- > forall (v, ks) in reversedMap.
    -- >   forall k in ks.
    -- >     (k, v) is in directMap
    reversedMap :: HashMap v (HashSet k)
  }
  deriving Show

emptyReversibleMap :: ReversibleMap k v
emptyReversibleMap = ReversibleMap HashMap.empty HashMap.empty

insertReversibleMap
  :: (Hashable k, Eq k, Hashable v, Eq v)
  => k
  -> v
  -> ReversibleMap k v
  -> ReversibleMap k v
insertReversibleMap k v rm = ReversibleMap
  { directMap = HashMap.insert k v (directMap rm)
  , reversedMap =
      let m' = case HashMap.lookup k (directMap rm) of
            Nothing -> reversedMap rm
            Just oldv -> HashMap.adjust (HashSet.delete k) oldv (reversedMap rm)
       in HashMap.insertWith HashSet.union v (HashSet.singleton k) m'
  }

reverseLookup :: (Hashable v, Eq v) => v -> ReversibleMap k v -> HashSet k
reverseLookup v rm = fromMaybe HashSet.empty $ HashMap.lookup v (reversedMap rm)

lookupReversibleMap :: (Hashable k, Eq k) => k -> ReversibleMap k v -> Maybe v
lookupReversibleMap k rm = HashMap.lookup k (directMap rm)
