{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Rank2Types    #-}
{-# LANGUAGE BangPatterns  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Packed.ST
-- Copyright   :  (c) Alberto Ruiz 2008
-- License     :  GPL-style
--
-- Maintainer  :  Alberto Ruiz <aruiz@um.es>
-- Stability   :  provisional
-- Portability :  portable
--
-- In-place manipulation inside the ST monad.
-- See examples/inplace.hs in the distribution.
--
-----------------------------------------------------------------------------

module Data.Packed.ST (
    -- * Mutable Vectors
    STVector, newVector, thawVector, freezeVector, runSTVector,
    readVector, writeVector, modifyVector, liftSTVector,
    -- * Mutable Matrices
    STMatrix, newMatrix, thawMatrix, freezeMatrix, runSTMatrix,
    readMatrix, writeMatrix, modifyMatrix, liftSTMatrix,
    -- * Unsafe functions
    newUndefinedVector,
    unsafeReadVector, unsafeWriteVector,
    unsafeThawVector, unsafeFreezeVector,
    newUndefinedMatrix,
    unsafeReadMatrix, unsafeWriteMatrix,
    unsafeThawMatrix, unsafeFreezeMatrix
) where

import Data.Packed.Internal

import Control.Monad.ST(ST, runST)
import Foreign.Storable(Storable, peekElemOff, pokeElemOff)

#if MIN_VERSION_base(4,4,0)
import Control.Monad.ST.Unsafe(unsafeIOToST)
#else
import Control.Monad.ST(unsafeIOToST)
#endif

{-# INLINE ioReadV #-}
ioReadV :: Storable t => Vector t -> Int -> IO t
ioReadV v k = unsafeWith v $ \s -> peekElemOff s k

{-# INLINE ioWriteV #-}
ioWriteV :: Storable t => Vector t -> Int -> t -> IO ()
ioWriteV v k x = unsafeWith v $ \s -> pokeElemOff s k x

newtype STVector s t = STVector (Vector t)

thawVector :: Storable t => Vector t -> ST s (STVector s t)
thawVector = unsafeIOToST . fmap STVector . cloneVector

unsafeThawVector :: Storable t => Vector t -> ST s (STVector s t)
unsafeThawVector = unsafeIOToST . return . STVector

runSTVector :: Storable t => (forall s . ST s (STVector s t)) -> Vector t
runSTVector st = runST (st >>= unsafeFreezeVector)

{-# INLINE unsafeReadVector #-}
unsafeReadVector :: Storable t => STVector s t -> Int -> ST s t
unsafeReadVector   (STVector x) = unsafeIOToST . ioReadV x

{-# INLINE unsafeWriteVector #-}
unsafeWriteVector :: Storable t => STVector s t -> Int -> t -> ST s ()
unsafeWriteVector  (STVector x) k = unsafeIOToST . ioWriteV x k

{-# INLINE modifyVector #-}
modifyVector :: (Storable t) => STVector s t -> Int -> (t -> t) -> ST s ()
modifyVector x k f = readVector x k >>= return . f >>= unsafeWriteVector x k

liftSTVector :: (Storable t) => (Vector t -> a) -> STVector s1 t -> ST s2 a
liftSTVector f (STVector x) = unsafeIOToST . fmap f . cloneVector $ x

freezeVector :: (Storable t) => STVector s1 t -> ST s2 (Vector t)
freezeVector v = liftSTVector id v

unsafeFreezeVector :: (Storable t) => STVector s1 t -> ST s2 (Vector t)
unsafeFreezeVector (STVector x) = unsafeIOToST . return $ x

{-# INLINE safeIndexV #-}
safeIndexV f (STVector v) k
    | k < 0 || k>= dim v = error $ "out of range error in vector (dim="
                                   ++show (dim v)++", pos="++show k++")"
    | otherwise = f (STVector v) k

{-# INLINE readVector #-}
readVector :: Storable t => STVector s t -> Int -> ST s t
readVector = safeIndexV unsafeReadVector

{-# INLINE writeVector #-}
writeVector :: Storable t => STVector s t -> Int -> t -> ST s ()
writeVector = safeIndexV unsafeWriteVector

newUndefinedVector :: Storable t => Int -> ST s (STVector s t)
newUndefinedVector = unsafeIOToST . fmap STVector . createVector

{-# INLINE newVector #-}
newVector :: Storable t => t -> Int -> ST s (STVector s t)
newVector x n = do
    v <- newUndefinedVector n
    let go (-1) = return v
        go !k = unsafeWriteVector v k x >> go (k-1 :: Int)
    go (n-1)

-------------------------------------------------------------------------

{-# INLINE ioReadM #-}
ioReadM :: Storable t => Matrix t -> Int -> Int -> IO t
ioReadM (Matrix _ nc cv RowMajor) r c = ioReadV cv (r*nc+c)
ioReadM (Matrix nr _ fv ColumnMajor) r c = ioReadV fv (c*nr+r)

{-# INLINE ioWriteM #-}
ioWriteM :: Storable t => Matrix t -> Int -> Int -> t -> IO ()
ioWriteM (Matrix _ nc cv RowMajor) r c val = ioWriteV cv (r*nc+c) val
ioWriteM (Matrix nr _ fv ColumnMajor) r c val = ioWriteV fv (c*nr+r) val

newtype STMatrix s t = STMatrix (Matrix t)

thawMatrix :: Storable t => Matrix t -> ST s (STMatrix s t)
thawMatrix = unsafeIOToST . fmap STMatrix . cloneMatrix

unsafeThawMatrix :: Storable t => Matrix t -> ST s (STMatrix s t)
unsafeThawMatrix = unsafeIOToST . return . STMatrix

runSTMatrix :: Storable t => (forall s . ST s (STMatrix s t)) -> Matrix t
runSTMatrix st = runST (st >>= unsafeFreezeMatrix)

{-# INLINE unsafeReadMatrix #-}
unsafeReadMatrix :: Storable t => STMatrix s t -> Int -> Int -> ST s t
unsafeReadMatrix   (STMatrix x) r = unsafeIOToST . ioReadM x r

{-# INLINE unsafeWriteMatrix #-}
unsafeWriteMatrix :: Storable t => STMatrix s t -> Int -> Int -> t -> ST s ()
unsafeWriteMatrix  (STMatrix x) r c = unsafeIOToST . ioWriteM x r c

{-# INLINE modifyMatrix #-}
modifyMatrix :: (Storable t) => STMatrix s t -> Int -> Int -> (t -> t) -> ST s ()
modifyMatrix x r c f = readMatrix x r c >>= return . f >>= unsafeWriteMatrix x r c

liftSTMatrix :: (Storable t) => (Matrix t -> a) -> STMatrix s1 t -> ST s2 a
liftSTMatrix f (STMatrix x) = unsafeIOToST . fmap f . cloneMatrix $ x

unsafeFreezeMatrix :: (Storable t) => STMatrix s1 t -> ST s2 (Matrix t)
unsafeFreezeMatrix (STMatrix x) = unsafeIOToST . return $ x

freezeMatrix :: (Storable t) => STMatrix s1 t -> ST s2 (Matrix t)
freezeMatrix m = liftSTMatrix id m

cloneMatrix (Matrix r c d o) = cloneVector d >>= return . (\d' -> Matrix r c d' o)

{-# INLINE safeIndexM #-}
safeIndexM f (STMatrix m) r c
    | r<0 || r>=rows m ||
      c<0 || c>=cols m = error $ "out of range error in matrix (size="
                                 ++show (rows m,cols m)++", pos="++show (r,c)++")"
    | otherwise = f (STMatrix m) r c

{-# INLINE readMatrix #-}
readMatrix :: Storable t => STMatrix s t -> Int -> Int -> ST s t
readMatrix = safeIndexM unsafeReadMatrix

{-# INLINE writeMatrix #-}
writeMatrix :: Storable t => STMatrix s t -> Int -> Int -> t -> ST s ()
writeMatrix = safeIndexM unsafeWriteMatrix

newUndefinedMatrix :: Storable t => MatrixOrder -> Int -> Int -> ST s (STMatrix s t)
newUndefinedMatrix ord r c = unsafeIOToST $ fmap STMatrix $ createMatrix ord r c

{-# NOINLINE newMatrix #-}
newMatrix :: Storable t => t -> Int -> Int -> ST s (STMatrix s t)
newMatrix v r c = unsafeThawMatrix $ reshape c $ runSTVector $ newVector v (r*c)
