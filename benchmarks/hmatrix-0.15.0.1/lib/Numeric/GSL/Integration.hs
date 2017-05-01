{-# OPTIONS #-}
-----------------------------------------------------------------------------
{- |
Module      :  Numeric.GSL.Integration
Copyright   :  (c) Alberto Ruiz 2006
License     :  GPL-style

Maintainer  :  Alberto Ruiz (aruiz at um dot es)
Stability   :  provisional
Portability :  uses ffi

Numerical integration routines.

<http://www.gnu.org/software/gsl/manual/html_node/Numerical-Integration.html#Numerical-Integration>
-}
-----------------------------------------------------------------------------

module Numeric.GSL.Integration (
    integrateQNG,
    integrateQAGS,
    integrateQAGI,
    integrateQAGIU,
    integrateQAGIL
) where

import Foreign.C.Types
import Foreign.Marshal.Alloc(malloc, free)
import Foreign.Ptr(Ptr, FunPtr, freeHaskellFunPtr)
import Foreign.Storable(peek)
import Data.Packed.Internal(check,(//))
import System.IO.Unsafe(unsafePerformIO)

{- | conversion of Haskell functions into function pointers that can be used in the C side
-}
foreign import ccall safe "wrapper" mkfun:: (Double -> Ptr() -> Double) -> IO( FunPtr (Double -> Ptr() -> Double)) 

--------------------------------------------------------------------
{- | Numerical integration using /gsl_integration_qags/ (adaptive integration with singularities). For example:

@\> let quad = integrateQAGS 1E-9 1000 
\> let f a x = x**(-0.5) * log (a*x)
\> quad (f 1) 0 1
(-3.999999999999974,4.871658632055187e-13)@
 
-}

integrateQAGS :: Double               -- ^ precision (e.g. 1E-9)
                 -> Int               -- ^ size of auxiliary workspace (e.g. 1000)
                 -> (Double -> Double) -- ^ function to be integrated on the interval (a,b)
                 -> Double           -- ^ a
                 -> Double           -- ^ b
                 -> (Double, Double) -- ^ result of the integration and error
integrateQAGS prec n f a b = unsafePerformIO $ do
    r <- malloc
    e <- malloc
    fp <- mkfun (\x _ -> f x) 
    c_integrate_qags fp a b prec (fromIntegral n) r e // check "integrate_qags"
    vr <- peek r
    ve <- peek e
    let result = (vr,ve)
    free r
    free e
    freeHaskellFunPtr fp
    return result

foreign import ccall safe "gsl-aux.h integrate_qags" 
 c_integrate_qags :: FunPtr (Double-> Ptr() -> Double) -> Double -> Double -> Double -> CInt
                     -> Ptr Double -> Ptr Double -> IO CInt

-----------------------------------------------------------------
{- | Numerical integration using /gsl_integration_qng/ (useful for fast integration of smooth functions). For example:

@\> let quad = integrateQNG 1E-6 
\> quad (\\x -> 4\/(1+x*x)) 0 1 
(3.141592653589793,3.487868498008632e-14)@
 
-}

integrateQNG :: Double               -- ^ precision (e.g. 1E-9)
                 -> (Double -> Double) -- ^ function to be integrated on the interval (a,b)
                 -> Double           -- ^ a
                 -> Double           -- ^ b
                 -> (Double, Double) -- ^ result of the integration and error
integrateQNG prec f a b = unsafePerformIO $ do
    r <- malloc
    e <- malloc
    fp <- mkfun (\x _ -> f x) 
    c_integrate_qng fp a b prec r e  // check "integrate_qng"
    vr <- peek r
    ve <- peek e
    let result = (vr,ve)
    free r
    free e
    freeHaskellFunPtr fp
    return result

foreign import ccall safe "gsl-aux.h integrate_qng" 
 c_integrate_qng :: FunPtr (Double-> Ptr() -> Double) -> Double -> Double -> Double 
                    -> Ptr Double -> Ptr Double -> IO CInt

--------------------------------------------------------------------
{- | Numerical integration using /gsl_integration_qagi/ (integration over the infinite integral -Inf..Inf using QAGS). 
For example:

@\> let quad = integrateQAGI 1E-9 1000 
\> let f a x = exp(-a * x^2)
\> quad (f 0.5) 
(2.5066282746310002,6.229215880648858e-11)@
 
-}

integrateQAGI :: Double               -- ^ precision (e.g. 1E-9)
                 -> Int               -- ^ size of auxiliary workspace (e.g. 1000)
                 -> (Double -> Double) -- ^ function to be integrated on the interval (-Inf,Inf)
                 -> (Double, Double) -- ^ result of the integration and error
integrateQAGI prec n f = unsafePerformIO $ do
    r <- malloc
    e <- malloc
    fp <- mkfun (\x _ -> f x) 
    c_integrate_qagi fp prec (fromIntegral n) r e // check "integrate_qagi"
    vr <- peek r
    ve <- peek e
    let result = (vr,ve)
    free r
    free e
    freeHaskellFunPtr fp
    return result

foreign import ccall safe "gsl-aux.h integrate_qagi" 
 c_integrate_qagi :: FunPtr (Double-> Ptr() -> Double) -> Double -> CInt
                     -> Ptr Double -> Ptr Double -> IO CInt

--------------------------------------------------------------------
{- | Numerical integration using /gsl_integration_qagiu/ (integration over the semi-infinite integral a..Inf). 
For example:

@\> let quad = integrateQAGIU 1E-9 1000 
\> let f a x = exp(-a * x^2)
\> quad (f 0.5) 0
(1.2533141373155001,3.114607940324429e-11)@
 
-}

integrateQAGIU :: Double               -- ^ precision (e.g. 1E-9)
                 -> Int               -- ^ size of auxiliary workspace (e.g. 1000)
                 -> (Double -> Double) -- ^ function to be integrated on the interval (a,Inf)
                 -> Double             -- ^ a
                 -> (Double, Double) -- ^ result of the integration and error
integrateQAGIU prec n f a = unsafePerformIO $ do
    r <- malloc
    e <- malloc
    fp <- mkfun (\x _ -> f x) 
    c_integrate_qagiu fp a prec (fromIntegral n) r e // check "integrate_qagiu"
    vr <- peek r
    ve <- peek e
    let result = (vr,ve)
    free r
    free e
    freeHaskellFunPtr fp
    return result

foreign import ccall safe "gsl-aux.h integrate_qagiu" 
 c_integrate_qagiu :: FunPtr (Double-> Ptr() -> Double) -> Double -> Double -> CInt
                     -> Ptr Double -> Ptr Double -> IO CInt

--------------------------------------------------------------------
{- | Numerical integration using /gsl_integration_qagil/ (integration over the semi-infinite integral -Inf..b). 
For example:

@\> let quad = integrateQAGIL 1E-9 1000 
\> let f a x = exp(-a * x^2)
\> quad (f 0.5) 0 
(1.2533141373155001,3.114607940324429e-11)@
 
-}

integrateQAGIL :: Double               -- ^ precision (e.g. 1E-9)
                 -> Int               -- ^ size of auxiliary workspace (e.g. 1000)
                 -> (Double -> Double) -- ^ function to be integrated on the interval (a,Inf)
                 -> Double             -- ^ b
                 -> (Double, Double) -- ^ result of the integration and error
integrateQAGIL prec n f b = unsafePerformIO $ do
    r <- malloc
    e <- malloc
    fp <- mkfun (\x _ -> f x) 
    c_integrate_qagil fp b prec (fromIntegral n) r e // check "integrate_qagil"
    vr <- peek r
    ve <- peek e
    let result = (vr,ve)
    free r
    free e
    freeHaskellFunPtr fp
    return result

foreign import ccall safe "gsl-aux.h integrate_qagil" 
 c_integrate_qagil :: FunPtr (Double-> Ptr() -> Double) -> Double -> Double -> CInt
                     -> Ptr Double -> Ptr Double -> IO CInt

