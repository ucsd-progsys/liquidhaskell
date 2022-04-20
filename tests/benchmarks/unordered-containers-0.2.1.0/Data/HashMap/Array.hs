{-# LANGUAGE BangPatterns, CPP, MagicHash, Rank2Types, UnboxedTuples #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

-- | Zero based arrays.
--
-- Note that no bounds checking are performed.
module Data.HashMap.Array
    ( Array
    , MArray

      -- * Creation
    , new
    , new_
    , singleton
    , singleton'
    , pair

      -- * Basic interface
    , length
    , lengthM
    , read
    , write
    , index
    , index_
    , indexM_
    , update
    , update'
    , updateWith
    , unsafeUpdate'
    , insert
    , insert'
    , delete
    , delete'

    , unsafeFreeze
    , unsafeThaw
    , run
    , run2
    , copy
    , copyM

      -- * Folds
    , foldl'
    , foldr

    , thaw
    , map
    , map'
    , traverse
    , filter
    ) where

import qualified Data.Traversable as Traversable
import Control.Applicative (Applicative)
import Control.DeepSeq
import Control.Monad.ST
import GHC.Exts
import GHC.ST (ST(..))
import Prelude hiding (filter, foldr, length, map, read)

------------------------------------------------------------------------

#if defined(ASSERTS)
-- This fugly hack is brought by GHC's apparent reluctance to deal
-- with MagicHash and UnboxedTuples when inferring types. Eek!
# define CHECK_BOUNDS(_func_,_len_,_k_) \
if (_k_) < 0 || (_k_) >= (_len_) then error ("Data.HashMap.Array." ++ (_func_) ++ ": bounds error, offset " ++ show (_k_) ++ ", length " ++ show (_len_)) else
# define CHECK_OP(_func_,_op_,_lhs_,_rhs_) \
if not ((_lhs_) _op_ (_rhs_)) then error ("Data.HashMap.Array." ++ (_func_) ++ ": Check failed: _lhs_ _op_ _rhs_ (" ++ show (_lhs_) ++ " vs. " ++ show (_rhs_) ++ ")") else
# define CHECK_GT(_func_,_lhs_,_rhs_) CHECK_OP(_func_,>,_lhs_,_rhs_)
# define CHECK_LE(_func_,_lhs_,_rhs_) CHECK_OP(_func_,<=,_lhs_,_rhs_)
#else
# define CHECK_BOUNDS(_func_,_len_,_k_)
# define CHECK_OP(_func_,_op_,_lhs_,_rhs_)
# define CHECK_GT(_func_,_lhs_,_rhs_)
# define CHECK_LE(_func_,_lhs_,_rhs_)
#endif

data Array a = Array {
      unArray :: !(Array# a)
#if __GLASGOW_HASKELL__ < 702
    , length :: !Int
#endif
    }

instance Show a => Show (Array a) where
    show = show . toList

#if __GLASGOW_HASKELL__ >= 702
length :: Array a -> Int
length ary = I# (sizeofArray# (unArray ary))
{-# INLINE length #-}
#endif

-- | Smart constructor
array :: Array# a -> Int -> Array a
#if __GLASGOW_HASKELL__ >= 702
array ary _n = Array ary
#else
array = Array
#endif
{-# INLINE array #-}

data MArray s a = MArray {
      unMArray :: !(MutableArray# s a)
#if __GLASGOW_HASKELL__ < 702
    , lengthM :: !Int
#endif
    }

#if __GLASGOW_HASKELL__ >= 702
lengthM :: MArray s a -> Int
lengthM mary = I# (sizeofMutableArray# (unMArray mary))
{-# INLINE lengthM #-}
#endif

-- | Smart constructor
marray :: MutableArray# s a -> Int -> MArray s a
#if __GLASGOW_HASKELL__ >= 702
marray mary _n = MArray mary
#else
marray = MArray
#endif
{-# INLINE marray #-}

------------------------------------------------------------------------

instance NFData a => NFData (Array a) where
    rnf = rnfArray

rnfArray :: NFData a => Array a -> ()
rnfArray ary0 = go ary0 n0 0
  where
    n0 = length ary0
    go !ary !n !i
        | i >= n = ()
        | otherwise = rnf (index ary i) `seq` go ary n (i+1)
{-# INLINE rnfArray #-}

-- | Create a new mutable array of specified size, in the specified
-- state thread, with each element containing the specified initial
-- value.
new :: Int -> a -> ST s (MArray s a)
new n@(I# n#) b =
    CHECK_GT("new",n,(0 :: Int))
    ST $ \s ->
        case newArray# n# b s of
            (# s', ary #) -> (# s', marray ary n #)
{-# INLINE new #-}

new_ :: Int -> ST s (MArray s a)
new_ n = new n undefinedElem

singleton :: a -> Array a
singleton x = runST (singleton' x)
{-# INLINE singleton #-}

singleton' :: a -> ST s (Array a)
singleton' x = new 1 x >>= unsafeFreeze
{-# INLINE singleton' #-}

pair :: a -> a -> Array a
pair x y = run $ do
    ary <- new 2 x
    write ary 1 y
    return ary
{-# INLINE pair #-}

read :: MArray s a -> Int -> ST s a
read ary _i@(I# i#) = ST $ \ s ->
    CHECK_BOUNDS("read", lengthM ary, _i)
        readArray# (unMArray ary) i# s
{-# INLINE read #-}

write :: MArray s a -> Int -> a -> ST s ()
write ary _i@(I# i#) b = ST $ \ s ->
    CHECK_BOUNDS("write", lengthM ary, _i)
        case writeArray# (unMArray ary) i# b s of
            s' -> (# s' , () #)
{-# INLINE write #-}

index :: Array a -> Int -> a
index ary _i@(I# i#) =
    CHECK_BOUNDS("index", length ary, _i)
        case indexArray# (unArray ary) i# of (# b #) -> b
{-# INLINE index #-}

index_ :: Array a -> Int -> ST s a
index_ ary _i@(I# i#) =
    CHECK_BOUNDS("index_", length ary, _i)
        case indexArray# (unArray ary) i# of (# b #) -> return b
{-# INLINE index_ #-}

indexM_ :: MArray s a -> Int -> ST s a
indexM_ ary _i@(I# i#) =
    CHECK_BOUNDS("index_", lengthM ary, _i)
        ST $ \ s# -> readArray# (unMArray ary) i# s#
{-# INLINE indexM_ #-}

unsafeFreeze :: MArray s a -> ST s (Array a)
unsafeFreeze mary
    = ST $ \s -> case unsafeFreezeArray# (unMArray mary) s of
                   (# s', ary #) -> (# s', array ary (lengthM mary) #)
{-# INLINE unsafeFreeze #-}

unsafeThaw :: Array a -> ST s (MArray s a)
unsafeThaw ary
    = ST $ \s -> case unsafeThawArray# (unArray ary) s of
                   (# s', mary #) -> (# s', marray mary (length ary) #)
{-# INLINE unsafeThaw #-}

run :: (forall s . ST s (MArray s e)) -> Array e
run act = runST $ act >>= unsafeFreeze
{-# INLINE run #-}

run2 :: (forall s. ST s (MArray s e, a)) -> (Array e, a)
run2 k = runST (do
                 (marr,b) <- k
                 arr <- unsafeFreeze marr
                 return (arr,b))

-- | Unsafely copy the elements of an array. Array bounds are not checked.
copy :: Array e -> Int -> MArray s e -> Int -> Int -> ST s ()
#if __GLASGOW_HASKELL__ >= 702
copy !src !_sidx@(I# sidx#) !dst !_didx@(I# didx#) _n@(I# n#) =
    CHECK_LE("copy", _sidx + _n, length src)
    CHECK_LE("copy", _didx + _n, lengthM dst)
        ST $ \ s# ->
        case copyArray# (unArray src) sidx# (unMArray dst) didx# n# s# of
            s2 -> (# s2, () #)
#else
copy !src !sidx !dst !didx n =
    CHECK_LE("copy", sidx + n, length src)
    CHECK_LE("copy", didx + n, lengthM dst)
        copy_loop sidx didx 0
  where
    copy_loop !i !j !c
        | c >= n = return ()
        | otherwise = do b <- index_ src i
                         write dst j b
                         copy_loop (i+1) (j+1) (c+1)
#endif

-- | Unsafely copy the elements of an array. Array bounds are not checked.
copyM :: MArray s e -> Int -> MArray s e -> Int -> Int -> ST s ()
#if __GLASGOW_HASKELL__ >= 702
copyM !src !_sidx@(I# sidx#) !dst !_didx@(I# didx#) _n@(I# n#) =
    CHECK_BOUNDS("copyM: src", lengthM src, _sidx + _n - 1)
    CHECK_BOUNDS("copyM: dst", lengthM dst, _didx + _n - 1)
    ST $ \ s# ->
    case copyMutableArray# (unMArray src) sidx# (unMArray dst) didx# n# s# of
        s2 -> (# s2, () #)
#else
copyM !src !sidx !dst !didx n =
    CHECK_BOUNDS("copyM: src", lengthM src, sidx + n - 1)
    CHECK_BOUNDS("copyM: dst", lengthM dst, didx + n - 1)
    copy_loop sidx didx 0
  where
    copy_loop !i !j !c
        | c >= n = return ()
        | otherwise = do b <- indexM_ src i
                         write dst j b
                         copy_loop (i+1) (j+1) (c+1)
#endif

-- | /O(n)/ Insert an element at the given position in this array,
-- increasing its size by one.
insert :: Array e -> Int -> e -> Array e
insert ary idx b = runST (insert' ary idx b)
{-# INLINE insert #-}

-- | /O(n)/ Insert an element at the given position in this array,
-- increasing its size by one.
insert' :: Array e -> Int -> e -> ST s (Array e)
insert' ary idx b =
    CHECK_BOUNDS("insert'", count + 1, idx)
        do mary <- new_ (count+1)
           copy ary 0 mary 0 idx
           write mary idx b
           copy ary idx mary (idx+1) (count-idx)
           unsafeFreeze mary
  where !count = length ary
{-# INLINE insert' #-}

-- | /O(n)/ Update the element at the given position in this array.
update :: Array e -> Int -> e -> Array e
update ary idx b = runST (update' ary idx b)
{-# INLINE update #-}

-- | /O(n)/ Update the element at the given position in this array.
update' :: Array e -> Int -> e -> ST s (Array e)
update' ary idx b =
    CHECK_BOUNDS("update'", count, idx)
        do mary <- thaw ary 0 count
           write mary idx b
           unsafeFreeze mary
  where !count = length ary
{-# INLINE update' #-}

-- | /O(n)/ Update the element at the given positio in this array, by
-- applying a function to it.  Evaluates the element to WHNF before
-- inserting it into the array.
updateWith :: Array e -> Int -> (e -> e) -> Array e
updateWith ary idx f = update ary idx $! f (index ary idx)
{-# INLINE updateWith #-}

-- | /O(1)/ Update the element at the given position in this array,
-- without copying.
unsafeUpdate' :: Array e -> Int -> e -> ST s ()
unsafeUpdate' ary idx b =
    CHECK_BOUNDS("unsafeUpdate'", length ary, idx)
        do mary <- unsafeThaw ary
           write mary idx b
           _ <- unsafeFreeze mary
           return ()
{-# INLINE unsafeUpdate' #-}

foldl' :: (b -> a -> b) -> b -> Array a -> b
foldl' f = \ z0 ary0 -> go ary0 (length ary0) 0 z0
  where
    go ary n i !z
        | i >= n    = z
        | otherwise = go ary n (i+1) (f z (index ary i))
{-# INLINE foldl' #-}

foldr :: (a -> b -> b) -> b -> Array a -> b
foldr f = \ z0 ary0 -> go ary0 (length ary0) 0 z0
  where
    go ary n i z
        | i >= n    = z
        | otherwise = f (index ary i) (go ary n (i+1) z)
{-# INLINE foldr #-}

undefinedElem :: a
undefinedElem = error "Data.HashMap.Array: Undefined element"
{-# NOINLINE undefinedElem #-}

thaw :: Array e -> Int -> Int -> ST s (MArray s e)
#if __GLASGOW_HASKELL__ >= 702
thaw !ary !_o@(I# o#) !n@(I# n#) =
    CHECK_LE("thaw", _o + n, length ary)
        ST $ \ s -> case thawArray# (unArray ary) o# n# s of
            (# s2, mary# #) -> (# s2, marray mary# n #)
#else
thaw !ary !o !n =
    CHECK_LE("thaw", o + n, length ary)
        do mary <- new_ n
           copy ary o mary 0 n
           return mary
#endif
{-# INLINE thaw #-}

-- | /O(n)/ Delete an element at the given position in this array,
-- decreasing its size by one.
delete :: Array e -> Int -> Array e
delete ary idx = runST (delete' ary idx)
{-# INLINE delete #-}

-- | /O(n)/ Delete an element at the given position in this array,
-- decreasing its size by one.
delete' :: Array e -> Int -> ST s (Array e)
delete' ary idx = do
    mary <- new_ (count-1)
    copy ary 0 mary 0 idx
    copy ary (idx+1) mary idx (count-(idx+1))
    unsafeFreeze mary
  where !count = length ary
{-# INLINE delete' #-}

map :: (a -> b) -> Array a -> Array b
map f = \ ary ->
    let !n = length ary
    in run $ do
        mary <- new_ n
        go ary mary 0 n
  where
    go ary mary i n
        | i >= n    = return mary
        | otherwise = do
             write mary i $ f (index ary i)
             go ary mary (i+1) n
{-# INLINE map #-}

-- | Strict version of 'map'.
map' :: (a -> b) -> Array a -> Array b
map' f = \ ary ->
    let !n = length ary
    in run $ do
        mary <- new_ n
        go ary mary 0 n
  where
    go ary mary i n
        | i >= n    = return mary
        | otherwise = do
             write mary i $! f (index ary i)
             go ary mary (i+1) n
{-# INLINE map' #-}

fromList :: Int -> [a] -> Array a
fromList n xs0 = run $ do
    mary <- new_ n
    go xs0 mary 0
  where
    go [] !mary !_   = return mary
    go (x:xs) mary i = do write mary i x
                          go xs mary (i+1)

toList :: Array a -> [a]
toList = foldr (:) []

traverse :: Applicative f => (a -> f b) -> Array a -> f (Array b)
traverse f = \ ary -> fromList (length ary) `fmap`
                      Traversable.traverse f (toList ary)
{-# INLINE traverse #-}

filter :: (a -> Bool) -> Array a -> Array a
filter p = \ ary ->
    let !n = length ary
    in run $ do
        mary <- new_ n
        go ary mary 0 0 n
  where
    go ary mary i j n
        | i >= n    = if i == j
                      then return mary
                      else do mary2 <- new_ j
                              copyM mary 0 mary2 0 j
                              return mary2
        | p el      = write mary j el >> go ary mary (i+1) (j+1) n
        | otherwise = go ary mary (i+1) j n
      where el = index ary i
{-# INLINE filter #-}
