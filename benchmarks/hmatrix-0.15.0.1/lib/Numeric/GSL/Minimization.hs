{-# LANGUAGE ForeignFunctionInterface #-}
-----------------------------------------------------------------------------
{- |
Module      :  Numeric.GSL.Minimization
Copyright   :  (c) Alberto Ruiz 2006-9
License     :  GPL-style

Maintainer  :  Alberto Ruiz (aruiz at um dot es)
Stability   :  provisional
Portability :  uses ffi

Minimization of a multidimensional function using some of the algorithms described in:

<http://www.gnu.org/software/gsl/manual/html_node/Multidimensional-Minimization.html>

The example in the GSL manual:

@

f [x,y] = 10*(x-1)^2 + 20*(y-2)^2 + 30

main = do
    let (s,p) = minimize NMSimplex2 1E-2 30 [1,1] f [5,7]
    print s
    print p

\> main
[0.9920430849306288,1.9969168063253182]
 0.000  512.500  1.130  6.500  5.000
 1.000  290.625  1.409  5.250  4.000
 2.000  290.625  1.409  5.250  4.000
 3.000  252.500  1.409  5.500  1.000
 ...
22.000   30.001  0.013  0.992  1.997
23.000   30.001  0.008  0.992  1.997
@

The path to the solution can be graphically shown by means of:

@'Graphics.Plot.mplot' $ drop 3 ('toColumns' p)@

Taken from the GSL manual:

The vector Broyden-Fletcher-Goldfarb-Shanno (BFGS) algorithm is a quasi-Newton method which builds up an approximation to the second derivatives of the function f using the difference between successive gradient vectors. By combining the first and second derivatives the algorithm is able to take Newton-type steps towards the function minimum, assuming quadratic behavior in that region.

The bfgs2 version of this minimizer is the most efficient version available, and is a faithful implementation of the line minimization scheme described in Fletcher's Practical Methods of Optimization, Algorithms 2.6.2 and 2.6.4. It supercedes the original bfgs routine and requires substantially fewer function and gradient evaluations. The user-supplied tolerance tol corresponds to the parameter \sigma used by Fletcher. A value of 0.1 is recommended for typical use (larger values correspond to less accurate line searches).

The nmsimplex2 version is a new O(N) implementation of the earlier O(N^2) nmsimplex minimiser. It calculates the size of simplex as the rms distance of each vertex from the center rather than the mean distance, which has the advantage of allowing a linear update.

-}

-----------------------------------------------------------------------------
module Numeric.GSL.Minimization (
    minimize, minimizeV, MinimizeMethod(..),
    minimizeD, minimizeVD, MinimizeMethodD(..),

    minimizeNMSimplex,
    minimizeConjugateGradient,
    minimizeVectorBFGS2
) where


import Data.Packed.Internal
import Data.Packed.Matrix
import Numeric.GSL.Internal

import Foreign.Ptr(Ptr, FunPtr, freeHaskellFunPtr)
import Foreign.C.Types
import System.IO.Unsafe(unsafePerformIO)

------------------------------------------------------------------------

{-# DEPRECATED minimizeNMSimplex "use minimize NMSimplex2 eps maxit sizes f xi" #-}
minimizeNMSimplex f xi szs eps maxit = minimize NMSimplex eps maxit szs f xi

{-# DEPRECATED minimizeConjugateGradient "use minimizeD ConjugateFR eps maxit step tol f g xi" #-}
minimizeConjugateGradient step tol eps maxit f g xi = minimizeD ConjugateFR eps maxit step tol f g xi

{-# DEPRECATED minimizeVectorBFGS2 "use minimizeD VectorBFGS2 eps maxit step tol f g xi" #-}
minimizeVectorBFGS2 step tol eps maxit f g xi = minimizeD VectorBFGS2 eps maxit step tol f g xi

-------------------------------------------------------------------------

data MinimizeMethod = NMSimplex
                    | NMSimplex2
                    deriving (Enum,Eq,Show,Bounded)

-- | Minimization without derivatives
minimize :: MinimizeMethod
         -> Double              -- ^ desired precision of the solution (size test)
         -> Int                 -- ^ maximum number of iterations allowed
         -> [Double]            -- ^ sizes of the initial search box
         -> ([Double] -> Double) -- ^ function to minimize
         -> [Double]            -- ^ starting point
         -> ([Double], Matrix Double) -- ^ solution vector and optimization path

-- | Minimization without derivatives (vector version)
minimizeV :: MinimizeMethod
         -> Double              -- ^ desired precision of the solution (size test)
         -> Int                 -- ^ maximum number of iterations allowed
         -> Vector Double       -- ^ sizes of the initial search box
         -> (Vector Double -> Double) -- ^ function to minimize
         -> Vector Double            -- ^ starting point
         -> (Vector Double, Matrix Double) -- ^ solution vector and optimization path

minimize method eps maxit sz f xi = v2l $ minimizeV method eps maxit (fromList sz) (f.toList) (fromList xi)
    where v2l (v,m) = (toList v, m)

ww2 w1 o1 w2 o2 f = w1 o1 $ \a1 -> w2 o2 $ \a2 -> f a1 a2

minimizeV method eps maxit szv f xiv = unsafePerformIO $ do
    let n   = dim xiv
    fp <- mkVecfun (iv f)
    rawpath <- ww2 vec xiv vec szv $ \xiv' szv' ->
                   createMIO maxit (n+3)
                         (c_minimize (fi (fromEnum method)) fp eps (fi maxit) // xiv' // szv')
                         "minimize"
    let it = round (rawpath @@> (maxit-1,0))
        path = takeRows it rawpath
        sol = cdat $ dropColumns 3 $ dropRows (it-1) path
    freeHaskellFunPtr fp
    return (sol, path)


foreign import ccall safe "gsl-aux.h minimize"
    c_minimize:: CInt -> FunPtr (CInt -> Ptr Double -> Double) -> Double -> CInt -> TVVM

----------------------------------------------------------------------------------


data MinimizeMethodD = ConjugateFR
                     | ConjugatePR
                     | VectorBFGS
                     | VectorBFGS2
                     | SteepestDescent
                     deriving (Enum,Eq,Show,Bounded)

-- | Minimization with derivatives.
minimizeD :: MinimizeMethodD
    -> Double                 -- ^ desired precision of the solution (gradient test)
    -> Int                    -- ^ maximum number of iterations allowed
    -> Double                 -- ^ size of the first trial step
    -> Double                 -- ^ tol (precise meaning depends on method)
    -> ([Double] -> Double)   -- ^ function to minimize
    -> ([Double] -> [Double]) -- ^ gradient
    -> [Double]               -- ^ starting point
    -> ([Double], Matrix Double) -- ^ solution vector and optimization path

-- | Minimization with derivatives (vector version)
minimizeVD :: MinimizeMethodD
    -> Double                 -- ^ desired precision of the solution (gradient test)
    -> Int                    -- ^ maximum number of iterations allowed
    -> Double                 -- ^ size of the first trial step
    -> Double                 -- ^ tol (precise meaning depends on method)
    -> (Vector Double -> Double)   -- ^ function to minimize
    -> (Vector Double -> Vector Double) -- ^ gradient
    -> Vector Double               -- ^ starting point
    -> (Vector Double, Matrix Double) -- ^ solution vector and optimization path

minimizeD method eps maxit istep tol f df xi = v2l $ minimizeVD
          method eps maxit istep tol (f.toList) (fromList.df.toList) (fromList xi)
    where v2l (v,m) = (toList v, m)


minimizeVD method eps maxit istep tol f df xiv = unsafePerformIO $ do
    let n = dim xiv
        f' = f
        df' = (checkdim1 n . df)
    fp <- mkVecfun (iv f')
    dfp <- mkVecVecfun (aux_vTov df')
    rawpath <- vec xiv $ \xiv' ->
                    createMIO maxit (n+2)
                         (c_minimizeD (fi (fromEnum method)) fp dfp istep tol eps (fi maxit) // xiv')
                         "minimizeD"
    let it = round (rawpath @@> (maxit-1,0))
        path = takeRows it rawpath
        sol = cdat $ dropColumns 2 $ dropRows (it-1) path
    freeHaskellFunPtr fp
    freeHaskellFunPtr dfp
    return (sol,path)

foreign import ccall safe "gsl-aux.h minimizeD"
    c_minimizeD :: CInt
                -> FunPtr (CInt -> Ptr Double -> Double)
                -> FunPtr TVV
                -> Double -> Double -> Double -> CInt
                -> TVM

---------------------------------------------------------------------

checkdim1 n v
    | dim v == n = v
    | otherwise = error $ "Error: "++ show n
                        ++ " components expected in the result of the gradient supplied to minimizeD"
