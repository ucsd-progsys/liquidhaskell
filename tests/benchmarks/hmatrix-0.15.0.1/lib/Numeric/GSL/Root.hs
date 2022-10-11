{- |
Module      :  Numeric.GSL.Root
Copyright   :  (c) Alberto Ruiz 2009
License     :  GPL

Maintainer  :  Alberto Ruiz (aruiz at um dot es)
Stability   :  provisional
Portability :  uses ffi

Multidimensional root finding.

<http://www.gnu.org/software/gsl/manual/html_node/Multidimensional-Root_002dFinding.html>

The example in the GSL manual:

@import Numeric.GSL
import Numeric.LinearAlgebra(format)
import Text.Printf(printf)

rosenbrock a b [x,y] = [ a*(1-x), b*(y-x^2) ]

disp = putStrLn . format \"  \" (printf \"%.3f\")

main = do
    let (sol,path) = root Hybrids 1E-7 30 (rosenbrock 1 10) [-10,-5]
    print sol
    disp path

\> main
[1.0,1.0]
 0.000  -10.000  -5.000  11.000  -1050.000
 1.000   -3.976  24.827   4.976     90.203
 2.000   -3.976  24.827   4.976     90.203
 3.000   -3.976  24.827   4.976     90.203
 4.000   -1.274  -5.680   2.274    -73.018
 5.000   -1.274  -5.680   2.274    -73.018
 6.000    0.249   0.298   0.751      2.359
 7.000    0.249   0.298   0.751      2.359
 8.000    1.000   0.878  -0.000     -1.218
 9.000    1.000   0.989  -0.000     -0.108
10.000    1.000   1.000   0.000      0.000
@

-}
-----------------------------------------------------------------------------

module Numeric.GSL.Root (
    uniRoot, UniRootMethod(..),
    uniRootJ, UniRootMethodJ(..),
    root, RootMethod(..),
    rootJ, RootMethodJ(..),
) where

import Data.Packed.Internal
import Data.Packed.Matrix
import Numeric.GSL.Internal
import Foreign.Ptr(FunPtr, freeHaskellFunPtr)
import Foreign.C.Types
import System.IO.Unsafe(unsafePerformIO)

-------------------------------------------------------------------------

data UniRootMethod = Bisection
                   | FalsePos
                   | Brent
                   deriving (Enum, Eq, Show, Bounded)

uniRoot :: UniRootMethod
        -> Double
        -> Int
        -> (Double -> Double)
        -> Double
        -> Double
        -> (Double, Matrix Double)
uniRoot method epsrel maxit fun xl xu = uniRootGen (fi (fromEnum method)) fun xl xu epsrel maxit

uniRootGen m f xl xu epsrel maxit = unsafePerformIO $ do
    fp <- mkDoublefun f
    rawpath <- createMIO maxit 4
                         (c_root m fp epsrel (fi maxit) xl xu)
                         "root"
    let it = round (rawpath @@> (maxit-1,0))
        path = takeRows it rawpath
        [sol] = toLists $ dropRows (it-1) path
    freeHaskellFunPtr fp
    return (sol !! 1, path)

foreign import ccall safe "root"
    c_root:: CInt -> FunPtr (Double -> Double) -> Double -> CInt -> Double -> Double -> TM

-------------------------------------------------------------------------
data UniRootMethodJ = UNewton
                    | Secant
                    | Steffenson
                    deriving (Enum, Eq, Show, Bounded)

uniRootJ :: UniRootMethodJ
        -> Double
        -> Int
        -> (Double -> Double)
        -> (Double -> Double)
        -> Double
        -> (Double, Matrix Double)
uniRootJ method epsrel maxit fun dfun x = uniRootJGen (fi (fromEnum method)) fun
    dfun x epsrel maxit

uniRootJGen m f df x epsrel maxit = unsafePerformIO $ do
    fp <- mkDoublefun f
    dfp <- mkDoublefun df
    rawpath <- createMIO maxit 2
                         (c_rootj m fp dfp epsrel (fi maxit) x)
                         "rootj"
    let it = round (rawpath @@> (maxit-1,0))
        path = takeRows it rawpath
        [sol] = toLists $ dropRows (it-1) path
    freeHaskellFunPtr fp
    return (sol !! 1, path)

foreign import ccall safe "rootj"
    c_rootj :: CInt -> FunPtr (Double -> Double) -> FunPtr (Double -> Double)
            -> Double -> CInt -> Double -> TM

-------------------------------------------------------------------------

data RootMethod = Hybrids
                | Hybrid
                | DNewton
                | Broyden
                deriving (Enum,Eq,Show,Bounded)

-- | Nonlinear multidimensional root finding using algorithms that do not require 
-- any derivative information to be supplied by the user.
-- Any derivatives needed are approximated by finite differences.
root :: RootMethod
     -> Double                     -- ^ maximum residual
     -> Int                        -- ^ maximum number of iterations allowed
     -> ([Double] -> [Double])     -- ^ function to minimize
     -> [Double]                   -- ^ starting point
     -> ([Double], Matrix Double)  -- ^ solution vector and optimization path

root method epsabs maxit fun xinit = rootGen (fi (fromEnum method)) fun xinit epsabs maxit

rootGen m f xi epsabs maxit = unsafePerformIO $ do
    let xiv = fromList xi
        n   = dim xiv
    fp <- mkVecVecfun (aux_vTov (checkdim1 n . fromList . f . toList))
    rawpath <- vec xiv $ \xiv' ->
                   createMIO maxit (2*n+1)
                         (c_multiroot m fp epsabs (fi maxit) // xiv')
                         "multiroot"
    let it = round (rawpath @@> (maxit-1,0))
        path = takeRows it rawpath
        [sol] = toLists $ dropRows (it-1) path
    freeHaskellFunPtr fp
    return (take n $ drop 1 sol, path)


foreign import ccall safe "multiroot"
    c_multiroot:: CInt -> FunPtr TVV -> Double -> CInt -> TVM

-------------------------------------------------------------------------

data RootMethodJ = HybridsJ
                 | HybridJ
                 | Newton
                 | GNewton
                deriving (Enum,Eq,Show,Bounded)

-- | Nonlinear multidimensional root finding using both the function and its derivatives.
rootJ :: RootMethodJ
      -> Double                     -- ^ maximum residual
      -> Int                        -- ^ maximum number of iterations allowed
      -> ([Double] -> [Double])     -- ^ function to minimize
      -> ([Double] -> [[Double]])   -- ^ Jacobian
      -> [Double]                   -- ^ starting point
      -> ([Double], Matrix Double)  -- ^ solution vector and optimization path

rootJ method epsabs maxit fun jac xinit = rootJGen (fi (fromEnum method)) fun jac xinit epsabs maxit

rootJGen m f jac xi epsabs maxit = unsafePerformIO $ do
    let xiv = fromList xi
        n   = dim xiv
    fp <- mkVecVecfun (aux_vTov (checkdim1 n . fromList . f . toList))
    jp <- mkVecMatfun (aux_vTom (checkdim2 n . fromLists . jac . toList))
    rawpath <- vec xiv $ \xiv' ->
                   createMIO maxit (2*n+1)
                         (c_multirootj m fp jp epsabs (fi maxit) // xiv')
                         "multiroot"
    let it = round (rawpath @@> (maxit-1,0))
        path = takeRows it rawpath
        [sol] = toLists $ dropRows (it-1) path
    freeHaskellFunPtr fp
    freeHaskellFunPtr jp
    return (take n $ drop 1 sol, path)

foreign import ccall safe "multirootj"
    c_multirootj:: CInt -> FunPtr TVV -> FunPtr TVM -> Double -> CInt -> TVM

-------------------------------------------------------

checkdim1 n v
    | dim v == n = v
    | otherwise = error $ "Error: "++ show n
                        ++ " components expected in the result of the function supplied to root"

checkdim2 n m
    | rows m == n && cols m == n = m
    | otherwise = error $ "Error: "++ show n ++ "x" ++ show n
                        ++ " Jacobian expected in rootJ"
