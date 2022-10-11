-----------------------------------------------------------------------------
-- |
-- Module      :  Numeric.GSL.Vector
-- Copyright   :  (c) Alberto Ruiz 2007
-- License     :  GPL-style
--
-- Maintainer  :  Alberto Ruiz <aruiz@um.es>
-- Stability   :  provisional
-- Portability :  portable (uses FFI)
--
-- Low level interface to vector operations.
--
-----------------------------------------------------------------------------

module Numeric.GSL.Vector (
    sumF, sumR, sumQ, sumC,
    prodF, prodR, prodQ, prodC,
    dotF, dotR, dotQ, dotC,
    FunCodeS(..), toScalarR, toScalarF, toScalarC, toScalarQ,
    FunCodeV(..), vectorMapR, vectorMapC, vectorMapF, vectorMapQ,
    FunCodeSV(..), vectorMapValR, vectorMapValC, vectorMapValF, vectorMapValQ,
    FunCodeVV(..), vectorZipR, vectorZipC, vectorZipF, vectorZipQ,
    RandDist(..), randomVector
) where

import Data.Packed.Internal.Common
import Data.Packed.Internal.Signatures
import Data.Packed.Internal.Vector

import Data.Complex
import Foreign.Marshal.Alloc(free)
import Foreign.Marshal.Array(newArray)
import Foreign.Ptr(Ptr)
import Foreign.C.Types
import System.IO.Unsafe(unsafePerformIO)

fromei x = fromIntegral (fromEnum x) :: CInt

data FunCodeV = Sin
              | Cos
              | Tan
              | Abs
              | ASin
              | ACos
              | ATan
              | Sinh
              | Cosh
              | Tanh
              | ASinh
              | ACosh
              | ATanh
              | Exp
              | Log
              | Sign
              | Sqrt
              deriving Enum

data FunCodeSV = Scale
               | Recip
               | AddConstant
               | Negate
               | PowSV
               | PowVS
               deriving Enum

data FunCodeVV = Add
               | Sub
               | Mul
               | Div
               | Pow
               | ATan2
               deriving Enum

data FunCodeS = Norm2
              | AbsSum
              | MaxIdx
              | Max
              | MinIdx
              | Min
              deriving Enum

------------------------------------------------------------------

-- | sum of elements
sumF :: Vector Float -> Float
sumF x = unsafePerformIO $ do
           r <- createVector 1
           app2 c_sumF vec x vec r "sumF"
           return $ r @> 0

-- | sum of elements
sumR :: Vector Double -> Double
sumR x = unsafePerformIO $ do
           r <- createVector 1
           app2 c_sumR vec x vec r "sumR"
           return $ r @> 0

-- | sum of elements
sumQ :: Vector (Complex Float) -> Complex Float
sumQ x = unsafePerformIO $ do
           r <- createVector 1
           app2 c_sumQ vec x vec r "sumQ"
           return $ r @> 0

-- | sum of elements
sumC :: Vector (Complex Double) -> Complex Double
sumC x = unsafePerformIO $ do
           r <- createVector 1
           app2 c_sumC vec x vec r "sumC"
           return $ r @> 0

foreign import ccall unsafe "gsl-aux.h sumF" c_sumF :: TFF
foreign import ccall unsafe "gsl-aux.h sumR" c_sumR :: TVV
foreign import ccall unsafe "gsl-aux.h sumQ" c_sumQ :: TQVQV
foreign import ccall unsafe "gsl-aux.h sumC" c_sumC :: TCVCV

-- | product of elements
prodF :: Vector Float -> Float
prodF x = unsafePerformIO $ do
           r <- createVector 1
           app2 c_prodF vec x vec r "prodF"
           return $ r @> 0

-- | product of elements
prodR :: Vector Double -> Double
prodR x = unsafePerformIO $ do
           r <- createVector 1
           app2 c_prodR vec x vec r "prodR"
           return $ r @> 0

-- | product of elements
prodQ :: Vector (Complex Float) -> Complex Float
prodQ x = unsafePerformIO $ do
           r <- createVector 1
           app2 c_prodQ vec x vec r "prodQ"
           return $ r @> 0

-- | product of elements
prodC :: Vector (Complex Double) -> Complex Double
prodC x = unsafePerformIO $ do
           r <- createVector 1
           app2 c_prodC vec x vec r "prodC"
           return $ r @> 0

foreign import ccall unsafe "gsl-aux.h prodF" c_prodF :: TFF
foreign import ccall unsafe "gsl-aux.h prodR" c_prodR :: TVV
foreign import ccall unsafe "gsl-aux.h prodQ" c_prodQ :: TQVQV
foreign import ccall unsafe "gsl-aux.h prodC" c_prodC :: TCVCV

-- | dot product
dotF :: Vector Float -> Vector Float -> Float
dotF x y = unsafePerformIO $ do
           r <- createVector 1
           app3 c_dotF vec x vec y vec r "dotF"
           return $ r @> 0

-- | dot product
dotR :: Vector Double -> Vector Double -> Double
dotR x y = unsafePerformIO $ do
           r <- createVector 1
           app3 c_dotR vec x vec y vec r "dotR"
           return $ r @> 0

-- | dot product
dotQ :: Vector (Complex Float) -> Vector (Complex Float) -> Complex Float
dotQ x y = unsafePerformIO $ do
           r <- createVector 1
           app3 c_dotQ vec x vec y vec r "dotQ"
           return $ r @> 0

-- | dot product
dotC :: Vector (Complex Double) -> Vector (Complex Double) -> Complex Double
dotC x y = unsafePerformIO $ do
           r <- createVector 1
           app3 c_dotC vec x vec y vec r "dotC"
           return $ r @> 0

foreign import ccall unsafe "gsl-aux.h dotF" c_dotF :: TFFF
foreign import ccall unsafe "gsl-aux.h dotR" c_dotR :: TVVV
foreign import ccall unsafe "gsl-aux.h dotQ" c_dotQ :: TQVQVQV
foreign import ccall unsafe "gsl-aux.h dotC" c_dotC :: TCVCVCV

------------------------------------------------------------------

toScalarAux fun code v = unsafePerformIO $ do
    r <- createVector 1
    app2 (fun (fromei code)) vec v vec r "toScalarAux"
    return (r `at` 0)

vectorMapAux fun code v = unsafePerformIO $ do
    r <- createVector (dim v)
    app2 (fun (fromei code)) vec v vec r "vectorMapAux"
    return r

vectorMapValAux fun code val v = unsafePerformIO $ do
    r <- createVector (dim v)
    pval <- newArray [val]
    app2 (fun (fromei code) pval) vec v vec r "vectorMapValAux"
    free pval
    return r

vectorZipAux fun code u v = unsafePerformIO $ do
    r <- createVector (dim u)
    app3 (fun (fromei code)) vec u vec v vec r "vectorZipAux"
    return r

---------------------------------------------------------------------

-- | obtains different functions of a vector: norm1, norm2, max, min, posmax, posmin, etc.
toScalarR :: FunCodeS -> Vector Double -> Double
toScalarR oper =  toScalarAux c_toScalarR (fromei oper)

foreign import ccall unsafe "gsl-aux.h toScalarR" c_toScalarR :: CInt -> TVV

-- | obtains different functions of a vector: norm1, norm2, max, min, posmax, posmin, etc.
toScalarF :: FunCodeS -> Vector Float -> Float
toScalarF oper =  toScalarAux c_toScalarF (fromei oper)

foreign import ccall unsafe "gsl-aux.h toScalarF" c_toScalarF :: CInt -> TFF

-- | obtains different functions of a vector: only norm1, norm2
toScalarC :: FunCodeS -> Vector (Complex Double) -> Double
toScalarC oper =  toScalarAux c_toScalarC (fromei oper)

foreign import ccall unsafe "gsl-aux.h toScalarC" c_toScalarC :: CInt -> TCVV

-- | obtains different functions of a vector: only norm1, norm2
toScalarQ :: FunCodeS -> Vector (Complex Float) -> Float
toScalarQ oper =  toScalarAux c_toScalarQ (fromei oper)

foreign import ccall unsafe "gsl-aux.h toScalarQ" c_toScalarQ :: CInt -> TQVF

------------------------------------------------------------------

-- | map of real vectors with given function
vectorMapR :: FunCodeV -> Vector Double -> Vector Double
vectorMapR = vectorMapAux c_vectorMapR

foreign import ccall unsafe "gsl-aux.h mapR" c_vectorMapR :: CInt -> TVV

-- | map of complex vectors with given function
vectorMapC :: FunCodeV -> Vector (Complex Double) -> Vector (Complex Double)
vectorMapC oper = vectorMapAux c_vectorMapC (fromei oper)

foreign import ccall unsafe "gsl-aux.h mapC" c_vectorMapC :: CInt -> TCVCV

-- | map of real vectors with given function
vectorMapF :: FunCodeV -> Vector Float -> Vector Float
vectorMapF = vectorMapAux c_vectorMapF

foreign import ccall unsafe "gsl-aux.h mapF" c_vectorMapF :: CInt -> TFF

-- | map of real vectors with given function
vectorMapQ :: FunCodeV -> Vector (Complex Float) -> Vector (Complex Float)
vectorMapQ = vectorMapAux c_vectorMapQ

foreign import ccall unsafe "gsl-aux.h mapQ" c_vectorMapQ :: CInt -> TQVQV

-------------------------------------------------------------------

-- | map of real vectors with given function
vectorMapValR :: FunCodeSV -> Double -> Vector Double -> Vector Double
vectorMapValR oper = vectorMapValAux c_vectorMapValR (fromei oper)

foreign import ccall unsafe "gsl-aux.h mapValR" c_vectorMapValR :: CInt -> Ptr Double -> TVV

-- | map of complex vectors with given function
vectorMapValC :: FunCodeSV -> Complex Double -> Vector (Complex Double) -> Vector (Complex Double)
vectorMapValC = vectorMapValAux c_vectorMapValC

foreign import ccall unsafe "gsl-aux.h mapValC" c_vectorMapValC :: CInt -> Ptr (Complex Double) -> TCVCV

-- | map of real vectors with given function
vectorMapValF :: FunCodeSV -> Float -> Vector Float -> Vector Float
vectorMapValF oper = vectorMapValAux c_vectorMapValF (fromei oper)

foreign import ccall unsafe "gsl-aux.h mapValF" c_vectorMapValF :: CInt -> Ptr Float -> TFF

-- | map of complex vectors with given function
vectorMapValQ :: FunCodeSV -> Complex Float -> Vector (Complex Float) -> Vector (Complex Float)
vectorMapValQ oper = vectorMapValAux c_vectorMapValQ (fromei oper)

foreign import ccall unsafe "gsl-aux.h mapValQ" c_vectorMapValQ :: CInt -> Ptr (Complex Float) -> TQVQV

-------------------------------------------------------------------

-- | elementwise operation on real vectors
vectorZipR :: FunCodeVV -> Vector Double -> Vector Double -> Vector Double
vectorZipR = vectorZipAux c_vectorZipR

foreign import ccall unsafe "gsl-aux.h zipR" c_vectorZipR :: CInt -> TVVV

-- | elementwise operation on complex vectors
vectorZipC :: FunCodeVV -> Vector (Complex Double) -> Vector (Complex Double) -> Vector (Complex Double)
vectorZipC = vectorZipAux c_vectorZipC

foreign import ccall unsafe "gsl-aux.h zipC" c_vectorZipC :: CInt -> TCVCVCV

-- | elementwise operation on real vectors
vectorZipF :: FunCodeVV -> Vector Float -> Vector Float -> Vector Float
vectorZipF = vectorZipAux c_vectorZipF

foreign import ccall unsafe "gsl-aux.h zipF" c_vectorZipF :: CInt -> TFFF

-- | elementwise operation on complex vectors
vectorZipQ :: FunCodeVV -> Vector (Complex Float) -> Vector (Complex Float) -> Vector (Complex Float)
vectorZipQ = vectorZipAux c_vectorZipQ

foreign import ccall unsafe "gsl-aux.h zipQ" c_vectorZipQ :: CInt -> TQVQVQV

-----------------------------------------------------------------------

data RandDist = Uniform  -- ^ uniform distribution in [0,1)
              | Gaussian -- ^ normal distribution with mean zero and standard deviation one
              deriving Enum

-- | Obtains a vector of pseudorandom elements from the the mt19937 generator in GSL, with a given seed. Use randomIO to get a random seed.
randomVector :: Int      -- ^ seed
             -> RandDist -- ^ distribution
             -> Int      -- ^ vector size
             -> Vector Double
randomVector seed dist n = unsafePerformIO $ do
    r <- createVector n
    app1 (c_random_vector (fi seed) ((fi.fromEnum) dist)) vec r "randomVector"
    return r

foreign import ccall unsafe "random_vector" c_random_vector :: CInt -> CInt -> TV
