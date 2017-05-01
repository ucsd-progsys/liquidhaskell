-- Module      :  Numeric.GSL.Internal
-- Copyright   :  (c) Alberto Ruiz 2009
-- License     :  GPL
--
-- Maintainer  :  Alberto Ruiz (aruiz at um dot es)
-- Stability   :  provisional
-- Portability :  uses ffi
--
-- Auxiliary functions.
--
-- #hide

module Numeric.GSL.Internal where

import Data.Packed.Internal

import Foreign.Marshal.Array(copyArray)
import Foreign.Ptr(Ptr, FunPtr)
import Foreign.C.Types
import System.IO.Unsafe(unsafePerformIO)

iv :: (Vector Double -> Double) -> (CInt -> Ptr Double -> Double)
iv f n p = f (createV (fromIntegral n) copy "iv") where
    copy n' q = do
        copyArray q p (fromIntegral n')
        return 0

-- | conversion of Haskell functions into function pointers that can be used in the C side
foreign import ccall safe "wrapper"
    mkVecfun :: (CInt -> Ptr Double -> Double)
             -> IO( FunPtr (CInt -> Ptr Double -> Double))

foreign import ccall safe "wrapper"
    mkVecVecfun :: TVV -> IO (FunPtr TVV)

foreign import ccall safe "wrapper"
    mkDoubleVecVecfun :: (Double -> TVV) -> IO (FunPtr (Double -> TVV))

foreign import ccall safe "wrapper"
    mkDoublefun :: (Double -> Double) -> IO (FunPtr (Double -> Double))

aux_vTov :: (Vector Double -> Vector Double) -> TVV
aux_vTov f n p nr r = g where
    v = f x
    x = createV (fromIntegral n) copy "aux_vTov"
    copy n' q = do
        copyArray q p (fromIntegral n')
        return 0
    g = do unsafeWith v $ \p' -> copyArray r p' (fromIntegral nr)
           return 0

foreign import ccall safe "wrapper"
    mkVecMatfun :: TVM -> IO (FunPtr TVM)

foreign import ccall safe "wrapper"
    mkDoubleVecMatfun :: (Double -> TVM) -> IO (FunPtr (Double -> TVM))

aux_vTom :: (Vector Double -> Matrix Double) -> TVM
aux_vTom f n p rr cr r = g where
    v = flatten $ f x
    x = createV (fromIntegral n) copy "aux_vTov"
    copy n' q = do
        copyArray q p (fromIntegral n')
        return 0
    g = do unsafeWith v $ \p' -> copyArray r p' (fromIntegral $ rr*cr)
           return 0

createV n fun msg = unsafePerformIO $ do
    r <- createVector n
    app1 fun vec r msg
    return r

createMIO r c fun msg = do
    res <- createMatrix RowMajor r c
    app1 fun mat res msg
    return res
