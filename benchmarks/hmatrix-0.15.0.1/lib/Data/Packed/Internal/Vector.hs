{-# LANGUAGE MagicHash, CPP, UnboxedTuples, BangPatterns, FlexibleContexts #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Packed.Internal.Vector
-- Copyright   :  (c) Alberto Ruiz 2007
-- License     :  GPL-style
--
-- Maintainer  :  Alberto Ruiz <aruiz@um.es>
-- Stability   :  provisional
-- Portability :  portable (uses FFI)
--
-- Vector implementation
--
-----------------------------------------------------------------------------

module Data.Packed.Internal.Vector (
    Vector, dim,
    fromList, toList, (|>),
    join, (@>), safe, at, at', subVector, takesV,
    mapVector, mapVectorWithIndex, zipVectorWith, unzipVectorWith,
    mapVectorM, mapVectorM_, mapVectorWithIndexM, mapVectorWithIndexM_,
    foldVector, foldVectorG, foldLoop, foldVectorWithIndex,
    createVector, vec,
    asComplex, asReal, float2DoubleV, double2FloatV,
    stepF, stepD, condF, condD,
    conjugateQ, conjugateC,
    fwriteVector, freadVector, fprintfVector, fscanfVector,
    cloneVector,
    unsafeToForeignPtr,
    unsafeFromForeignPtr,
    unsafeWith
) where

import Data.Packed.Internal.Common
import Data.Packed.Internal.Signatures
import Foreign.Marshal.Alloc(free)
import Foreign.Marshal.Array(peekArray, pokeArray, copyArray, advancePtr)
import Foreign.ForeignPtr(ForeignPtr, castForeignPtr)
import Foreign.Ptr(Ptr)
import Foreign.Storable(Storable, peekElemOff, pokeElemOff, sizeOf)
import Foreign.C.String
import Foreign.C.Types
import Data.Complex
import Control.Monad(when)
import System.IO.Unsafe(unsafePerformIO)

#if __GLASGOW_HASKELL__ >= 605
import GHC.ForeignPtr           (mallocPlainForeignPtrBytes)
#else
import Foreign.ForeignPtr       (mallocForeignPtrBytes)
#endif

import GHC.Base
#if __GLASGOW_HASKELL__ < 612
import GHC.IOBase hiding (liftIO)
#endif

import qualified Data.Vector.Storable as Vector
import Data.Vector.Storable(Vector,
                            unsafeToForeignPtr,
                            unsafeFromForeignPtr,
                            unsafeWith)


-- | Number of elements
dim :: (Storable t) => Vector t -> Int
dim = Vector.length


-- C-Haskell vector adapter
-- vec :: Adapt (CInt -> Ptr t -> r) (Vector t) r
vec :: (Storable t) => Vector t -> (((CInt -> Ptr t -> t1) -> t1) -> IO b) -> IO b
vec x f = unsafeWith x $ \p -> do
    let v g = do
        g (fi $ dim x) p
    f v
{-# INLINE vec #-}


-- allocates memory for a new vector
createVector :: Storable a => Int -> IO (Vector a)
createVector n = do
    when (n <= 0) $ error ("trying to createVector of dim "++show n)
    fp <- doMalloc undefined
    return $ unsafeFromForeignPtr fp 0 n
  where
    --
    -- Use the much cheaper Haskell heap allocated storage
    -- for foreign pointer space we control
    --
    doMalloc :: Storable b => b -> IO (ForeignPtr b)
    doMalloc dummy = do
#if __GLASGOW_HASKELL__ >= 605
        mallocPlainForeignPtrBytes (n * sizeOf dummy)
#else
        mallocForeignPtrBytes      (n * sizeOf dummy)
#endif

{- | creates a Vector from a list:

@> fromList [2,3,5,7]
4 |> [2.0,3.0,5.0,7.0]@

-}
fromList :: Storable a => [a] -> Vector a
fromList l = unsafePerformIO $ do
    v <- createVector (length l)
    unsafeWith v $ \ p -> pokeArray p l
    return v

safeRead v = inlinePerformIO . unsafeWith v
{-# INLINE safeRead #-}

inlinePerformIO :: IO a -> a
inlinePerformIO (IO m) = case m realWorld# of (# _, r #) -> r
{-# INLINE inlinePerformIO #-}

{- | extracts the Vector elements to a list

@> toList (linspace 5 (1,10))
[1.0,3.25,5.5,7.75,10.0]@

-}
toList :: Storable a => Vector a -> [a]
toList v = safeRead v $ peekArray (dim v)

{- | An alternative to 'fromList' with explicit dimension. The input
     list is explicitly truncated if it is too long, so it may safely
     be used, for instance, with infinite lists.

     This is the format used in the instances for Show (Vector a).
-}
(|>) :: (Storable a) => Int -> [a] -> Vector a
infixl 9 |>
n |> l = if length l' == n
            then fromList l'
            else error "list too short for |>"
  where l' = take n l


-- | access to Vector elements without range checking
at' :: Storable a => Vector a -> Int -> a
at' v n = safeRead v $ flip peekElemOff n
{-# INLINE at' #-}

--
-- turn off bounds checking with -funsafe at configure time.
-- ghc will optimise away the salways true case at compile time.
--
#if defined(UNSAFE)
safe :: Bool
safe = False
#else
safe = True
#endif

-- | access to Vector elements with range checking.
at :: Storable a => Vector a -> Int -> a
at v n
    | safe      = if n >= 0 && n < dim v
                    then at' v n
                    else error "vector index out of range"
    | otherwise = at' v n
{-# INLINE at #-}

{- | takes a number of consecutive elements from a Vector

@> subVector 2 3 (fromList [1..10])
3 |> [3.0,4.0,5.0]@

-}
subVector :: Storable t => Int       -- ^ index of the starting element
                        -> Int       -- ^ number of elements to extract
                        -> Vector t  -- ^ source
                        -> Vector t  -- ^ result
subVector = Vector.slice


{- | Reads a vector position:

@> fromList [0..9] \@\> 7
7.0@

-}
(@>) :: Storable t => Vector t -> Int -> t
infixl 9 @>
(@>) = at


{- | creates a new Vector by joining a list of Vectors

@> join [fromList [1..5], constant 1 3]
8 |> [1.0,2.0,3.0,4.0,5.0,1.0,1.0,1.0]@

-}
join :: Storable t => [Vector t] -> Vector t
join [] = error "joining zero vectors"
join [v] = v
join as = unsafePerformIO $ do
    let tot = sum (map dim as)
    r <- createVector tot
    unsafeWith r $ \ptr ->
        joiner as tot ptr
    return r
  where joiner [] _ _ = return ()
        joiner (v:cs) _ p = do
            let n = dim v
            unsafeWith v $ \pb -> copyArray p pb n
            joiner cs 0 (advancePtr p n)


{- | Extract consecutive subvectors of the given sizes.

@> takesV [3,4] (linspace 10 (1,10))
[3 |> [1.0,2.0,3.0],4 |> [4.0,5.0,6.0,7.0]]@

-}
takesV :: Storable t => [Int] -> Vector t -> [Vector t]
takesV ms w | sum ms > dim w = error $ "takesV " ++ show ms ++ " on dim = " ++ (show $ dim w)
            | otherwise = go ms w
    where go [] _ = []
          go (n:ns) v = subVector 0 n v
                      : go ns (subVector n (dim v - n) v)

---------------------------------------------------------------

-- | transforms a complex vector into a real vector with alternating real and imaginary parts 
asReal :: (RealFloat a, Storable a) => Vector (Complex a) -> Vector a
asReal v = unsafeFromForeignPtr (castForeignPtr fp) (2*i) (2*n)
    where (fp,i,n) = unsafeToForeignPtr v

-- | transforms a real vector into a complex vector with alternating real and imaginary parts
asComplex :: (RealFloat a, Storable a) => Vector a -> Vector (Complex a)
asComplex v = unsafeFromForeignPtr (castForeignPtr fp) (i `div` 2) (n `div` 2)
    where (fp,i,n) = unsafeToForeignPtr v

---------------------------------------------------------------

float2DoubleV :: Vector Float -> Vector Double
float2DoubleV v = unsafePerformIO $ do
    r <- createVector (dim v)
    app2 c_float2double vec v vec r "float2double"
    return r

double2FloatV :: Vector Double -> Vector Float
double2FloatV v = unsafePerformIO $ do
    r <- createVector (dim v)
    app2 c_double2float vec v vec r "double2float2"
    return r


foreign import ccall unsafe "float2double" c_float2double:: TFV
foreign import ccall unsafe "double2float" c_double2float:: TVF

---------------------------------------------------------------

stepF :: Vector Float -> Vector Float
stepF v = unsafePerformIO $ do
    r <- createVector (dim v)
    app2 c_stepF vec v vec r "stepF"
    return r

stepD :: Vector Double -> Vector Double
stepD v = unsafePerformIO $ do
    r <- createVector (dim v)
    app2 c_stepD vec v vec r "stepD"
    return r

foreign import ccall unsafe "stepF" c_stepF :: TFF
foreign import ccall unsafe "stepD" c_stepD :: TVV

---------------------------------------------------------------

condF :: Vector Float -> Vector Float -> Vector Float -> Vector Float -> Vector Float -> Vector Float
condF x y l e g = unsafePerformIO $ do
    r <- createVector (dim x)
    app6 c_condF vec x vec y vec l vec e vec g vec r "condF"
    return r

condD :: Vector Double -> Vector Double -> Vector Double -> Vector Double -> Vector Double -> Vector Double
condD x y l e g = unsafePerformIO $ do
    r <- createVector (dim x)
    app6 c_condD vec x vec y vec l vec e vec g vec r "condD"
    return r

foreign import ccall unsafe "condF" c_condF :: CInt -> PF -> CInt -> PF -> CInt -> PF -> TFFF
foreign import ccall unsafe "condD" c_condD :: CInt -> PD -> CInt -> PD -> CInt -> PD -> TVVV

--------------------------------------------------------------------------------

conjugateAux fun x = unsafePerformIO $ do
    v <- createVector (dim x)
    app2 fun vec x vec v "conjugateAux"
    return v

conjugateQ :: Vector (Complex Float) -> Vector (Complex Float)
conjugateQ = conjugateAux c_conjugateQ
foreign import ccall unsafe "conjugateQ" c_conjugateQ :: TQVQV

conjugateC :: Vector (Complex Double) -> Vector (Complex Double)
conjugateC = conjugateAux c_conjugateC
foreign import ccall unsafe "conjugateC" c_conjugateC :: TCVCV

--------------------------------------------------------------------------------

cloneVector :: Storable t => Vector t -> IO (Vector t)
cloneVector v = do
        let n = dim v
        r <- createVector n
        let f _ s _ d =  copyArray d s n >> return 0
        app2 f vec v vec r "cloneVector"
        return r

------------------------------------------------------------------

-- | map on Vectors
mapVector :: (Storable a, Storable b) => (a-> b) -> Vector a -> Vector b
mapVector f v = unsafePerformIO $ do
    w <- createVector (dim v)
    unsafeWith v $ \p ->
        unsafeWith w $ \q -> do
            let go (-1) = return ()
                go !k = do x <- peekElemOff p k
                           pokeElemOff      q k (f x)
                           go (k-1)
            go (dim v -1)
    return w
{-# INLINE mapVector #-}

-- | zipWith for Vectors
zipVectorWith :: (Storable a, Storable b, Storable c) => (a-> b -> c) -> Vector a -> Vector b -> Vector c
zipVectorWith f u v = unsafePerformIO $ do
    let n = min (dim u) (dim v)
    w <- createVector n
    unsafeWith u $ \pu ->
        unsafeWith v $ \pv ->
            unsafeWith w $ \pw -> do
                let go (-1) = return ()
                    go !k = do x <- peekElemOff pu k
                               y <- peekElemOff pv k
                               pokeElemOff      pw k (f x y)
                               go (k-1)
                go (n -1)
    return w
{-# INLINE zipVectorWith #-}

-- | unzipWith for Vectors
unzipVectorWith :: (Storable (a,b), Storable c, Storable d) 
                   => ((a,b) -> (c,d)) -> Vector (a,b) -> (Vector c,Vector d)
unzipVectorWith f u = unsafePerformIO $ do
      let n = dim u
      v <- createVector n
      w <- createVector n
      unsafeWith u $ \pu ->
          unsafeWith v $ \pv ->
              unsafeWith w $ \pw -> do
                  let go (-1) = return ()
                      go !k   = do z <- peekElemOff pu k
                                   let (x,y) = f z 
                                   pokeElemOff      pv k x
                                   pokeElemOff      pw k y
                                   go (k-1)
                  go (n-1)
      return (v,w)
{-# INLINE unzipVectorWith #-}

foldVector :: Storable a => (a -> b -> b) -> b -> Vector a -> b
foldVector f x v = unsafePerformIO $
    unsafeWith v $ \p -> do
        let go (-1) s = return s
            go !k !s = do y <- peekElemOff p k
                          go (k-1::Int) (f y s)
        go (dim v -1) x
{-# INLINE foldVector #-}

-- the zero-indexed index is passed to the folding function
foldVectorWithIndex :: Storable a => (Int -> a -> b -> b) -> b -> Vector a -> b
foldVectorWithIndex f x v = unsafePerformIO $
    unsafeWith v $ \p -> do
        let go (-1) s = return s
            go !k !s = do y <- peekElemOff p k
                          go (k-1::Int) (f k y s)
        go (dim v -1) x
{-# INLINE foldVectorWithIndex #-}

foldLoop f s0 d = go (d - 1) s0
     where
       go 0 s = f (0::Int) s
       go !j !s = go (j - 1) (f j s)

foldVectorG f s0 v = foldLoop g s0 (dim v)
    where g !k !s = f k (at' v) s
          {-# INLINE g #-} -- Thanks to Ryan Ingram (http://permalink.gmane.org/gmane.comp.lang.haskell.cafe/46479)
{-# INLINE foldVectorG #-}

-------------------------------------------------------------------

-- | monadic map over Vectors
--    the monad @m@ must be strict
mapVectorM :: (Storable a, Storable b, Monad m) => (a -> m b) -> Vector a -> m (Vector b)
mapVectorM f v = do
    w <- return $! unsafePerformIO $! createVector (dim v)
    mapVectorM' w 0 (dim v -1)
    return w
    where mapVectorM' w' !k !t
              | k == t               = do
                                       x <- return $! inlinePerformIO $! unsafeWith v $! \p -> peekElemOff p k 
                                       y <- f x
                                       return $! inlinePerformIO $! unsafeWith w' $! \q -> pokeElemOff q k y
              | otherwise            = do
                                       x <- return $! inlinePerformIO $! unsafeWith v $! \p -> peekElemOff p k 
                                       y <- f x
                                       _ <- return $! inlinePerformIO $! unsafeWith w' $! \q -> pokeElemOff q k y
                                       mapVectorM' w' (k+1) t
{-# INLINE mapVectorM #-}

-- | monadic map over Vectors
mapVectorM_ :: (Storable a, Monad m) => (a -> m ()) -> Vector a -> m ()
mapVectorM_ f v = do
    mapVectorM' 0 (dim v -1)
    where mapVectorM' !k !t
              | k == t            = do
                                    x <- return $! inlinePerformIO $! unsafeWith v $! \p -> peekElemOff p k
                                    f x
              | otherwise         = do
                                    x <- return $! inlinePerformIO $! unsafeWith v $! \p -> peekElemOff p k 
                                    _ <- f x
                                    mapVectorM' (k+1) t
{-# INLINE mapVectorM_ #-}

-- | monadic map over Vectors with the zero-indexed index passed to the mapping function
--    the monad @m@ must be strict
mapVectorWithIndexM :: (Storable a, Storable b, Monad m) => (Int -> a -> m b) -> Vector a -> m (Vector b)
mapVectorWithIndexM f v = do
    w <- return $! unsafePerformIO $! createVector (dim v)
    mapVectorM' w 0 (dim v -1)
    return w
    where mapVectorM' w' !k !t
              | k == t               = do
                                       x <- return $! inlinePerformIO $! unsafeWith v $! \p -> peekElemOff p k 
                                       y <- f k x
                                       return $! inlinePerformIO $! unsafeWith w' $! \q -> pokeElemOff q k y
              | otherwise            = do
                                       x <- return $! inlinePerformIO $! unsafeWith v $! \p -> peekElemOff p k 
                                       y <- f k x
                                       _ <- return $! inlinePerformIO $! unsafeWith w' $! \q -> pokeElemOff q k y
                                       mapVectorM' w' (k+1) t
{-# INLINE mapVectorWithIndexM #-}

-- | monadic map over Vectors with the zero-indexed index passed to the mapping function
mapVectorWithIndexM_ :: (Storable a, Monad m) => (Int -> a -> m ()) -> Vector a -> m ()
mapVectorWithIndexM_ f v = do
    mapVectorM' 0 (dim v -1)
    where mapVectorM' !k !t
              | k == t            = do
                                    x <- return $! inlinePerformIO $! unsafeWith v $! \p -> peekElemOff p k
                                    f k x
              | otherwise         = do
                                    x <- return $! inlinePerformIO $! unsafeWith v $! \p -> peekElemOff p k 
                                    _ <- f k x
                                    mapVectorM' (k+1) t
{-# INLINE mapVectorWithIndexM_ #-}


mapVectorWithIndex :: (Storable a, Storable b) => (Int -> a -> b) -> Vector a -> Vector b
--mapVectorWithIndex g = head . mapVectorWithIndexM (\a b -> [g a b])
mapVectorWithIndex f v = unsafePerformIO $ do
    w <- createVector (dim v)
    unsafeWith v $ \p ->
        unsafeWith w $ \q -> do
            let go (-1) = return ()
                go !k = do x <- peekElemOff p k
                           pokeElemOff      q k (f k x)
                           go (k-1)
            go (dim v -1)
    return w
{-# INLINE mapVectorWithIndex #-}

-------------------------------------------------------------------


-- | Loads a vector from an ASCII file (the number of elements must be known in advance).
fscanfVector :: FilePath -> Int -> IO (Vector Double)
fscanfVector filename n = do
    charname <- newCString filename
    res <- createVector n
    app1 (gsl_vector_fscanf charname) vec res "gsl_vector_fscanf"
    free charname
    return res

foreign import ccall unsafe "vector_fscanf" gsl_vector_fscanf:: Ptr CChar -> TV

-- | Saves the elements of a vector, with a given format (%f, %e, %g), to an ASCII file.
fprintfVector :: FilePath -> String -> Vector Double -> IO ()
fprintfVector filename fmt v = do
    charname <- newCString filename
    charfmt <- newCString fmt
    app1 (gsl_vector_fprintf charname charfmt) vec v "gsl_vector_fprintf"
    free charname
    free charfmt

foreign import ccall unsafe "vector_fprintf" gsl_vector_fprintf :: Ptr CChar -> Ptr CChar -> TV

-- | Loads a vector from a binary file (the number of elements must be known in advance).
freadVector :: FilePath -> Int -> IO (Vector Double)
freadVector filename n = do
    charname <- newCString filename
    res <- createVector n
    app1 (gsl_vector_fread charname) vec res "gsl_vector_fread"
    free charname
    return res

foreign import ccall unsafe "vector_fread" gsl_vector_fread:: Ptr CChar -> TV

-- | Saves the elements of a vector to a binary file.
fwriteVector :: FilePath -> Vector Double -> IO ()
fwriteVector filename v = do
    charname <- newCString filename
    app1 (gsl_vector_fwrite charname) vec v "gsl_vector_fwrite"
    free charname

foreign import ccall unsafe "vector_fwrite" gsl_vector_fwrite :: Ptr CChar -> TV

