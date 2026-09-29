{-# LANGUAGE BangPatterns #-}

-- | A cache retaining every loaded value for reuse. The lock covers a miss and
-- insertion, so concurrent readers reuse the same entry.
module Language.Haskell.Liquid.GHC.Plugin.Cache
  ( Cache, newCache, cached ) where

import Control.Concurrent.MVar
import qualified Data.Map.Strict as M

-- | A mutable map from keys @k@ to retained values @v@, protected by an 'MVar'.
newtype Cache k v = Cache (MVar (M.Map k v))

newCache :: IO (Cache k v)
newCache = Cache <$> newMVar M.empty

-- | The cached function returns a retained value for a key,
-- or runs the supplied loader on a miss.
--
-- Side Effects:
-- * The cache lock covers lookup, loading, and updating the state.
-- * A loaded value and the updated map are evaluated to weak head normal form
--   before publishing the state. Values are not deeply evaluated.
--   This keeps evaluation failures inside 'modifyMVar', which restores the
--   previous state on exception instead of publishing a failing thunk.
-- * The loader must not call 'cached' on this same cache, or wait for another
--   operation that needs its lock. The lock is held while the loader runs,
--   so such a dependency would deadlock.
cached
  :: Ord k
  => Cache k v
  -- ^ Shared mutable cache to query and update.
  -> k
  -- ^ Identity of the requested value.
  -> IO v
  -- ^ Action that loads the value on a miss, while holding the cache lock.
  -> IO v
  -- ^ The retained or newly loaded value. Loader and cache-update exceptions propagate.
cached (Cache state) key load =
  modifyMVar state $ \entries ->
    case M.lookup key entries of
      Just value -> pure (entries, value)
      Nothing -> do
        !value <- load
        let !entries' = M.insert key value entries
        pure (entries', value)
