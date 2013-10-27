{- |
Module      :  Numeric.GSL.Fitting
Copyright   :  (c) Alberto Ruiz 2010
License     :  GPL

Maintainer  :  Alberto Ruiz (aruiz at um dot es)
Stability   :  provisional
Portability :  uses ffi

Nonlinear Least-Squares Fitting

<http://www.gnu.org/software/gsl/manual/html_node/Nonlinear-Least_002dSquares-Fitting.html>

The example program in the GSL manual (see examples/fitting.hs):

@dat = [
 ([0.0],([6.0133918608118675],0.1)),
 ([1.0],([5.5153769909966535],0.1)),
 ([2.0],([5.261094606015287],0.1)),
 ...
 ([39.0],([1.0619821710802808],0.1))]

expModel [a,lambda,b] [t] = [a * exp (-lambda * t) + b]

expModelDer [a,lambda,b] [t] = [[exp (-lambda * t), -t * a * exp(-lambda*t) , 1]]

(sol,path) = fitModelScaled 1E-4 1E-4 20 (expModel, expModelDer) dat [1,0,0]

\> path
(6><5)
 [ 1.0,  76.45780563978782, 1.6465931240727802, 1.8147715267618197e-2, 0.6465931240727797
 , 2.0, 37.683816318260355,  2.858760367632973,  8.092094813253975e-2, 1.4479636296208662
 , 3.0,    9.5807893736187,  4.948995119561291,   0.11942927999921617, 1.0945766509238248
 , 4.0,  5.630494933603935,  5.021755718065913,   0.10287787128056883, 1.0338835440862608
 , 5.0,  5.443976278682909,  5.045204331329302,   0.10405523433131504,  1.019416067207375
 , 6.0, 5.4439736648994685,  5.045357818922331,   0.10404905846029407, 1.0192487112786812 ]
\> sol
[(5.045357818922331,6.027976702418132e-2),
(0.10404905846029407,3.157045047172834e-3),
(1.0192487112786812,3.782067731353722e-2)]@

-}
-----------------------------------------------------------------------------

module Numeric.GSL.Fitting (
    -- * Levenberg-Marquardt
    nlFitting, FittingMethod(..),
    -- * Utilities
    fitModelScaled, fitModel
) where

import Data.Packed.Internal
import Numeric.LinearAlgebra
import Numeric.GSL.Internal

import Foreign.Ptr(FunPtr, freeHaskellFunPtr)
import Foreign.C.Types
import System.IO.Unsafe(unsafePerformIO)

-------------------------------------------------------------------------

data FittingMethod = LevenbergMarquardtScaled -- ^ Interface to gsl_multifit_fdfsolver_lmsder. This is a robust and efficient version of the Levenberg-Marquardt algorithm as implemented in the scaled lmder routine in minpack. Minpack was written by Jorge J. More, Burton S. Garbow and Kenneth E. Hillstrom.
                   | LevenbergMarquardt -- ^ This is an unscaled version of the lmder algorithm. The elements of the diagonal scaling matrix D are set to 1. This algorithm may be useful in circumstances where the scaled version of lmder converges too slowly, or the function is already scaled appropriately.
        deriving (Enum,Eq,Show,Bounded)


-- | Nonlinear multidimensional least-squares fitting.
nlFitting :: FittingMethod
      -> Double                     -- ^ absolute tolerance
      -> Double                     -- ^ relative tolerance
      -> Int                        -- ^ maximum number of iterations allowed
      -> (Vector Double -> Vector Double)     -- ^ function to be minimized
      -> (Vector Double -> Matrix Double)   -- ^ Jacobian
      -> Vector Double                   -- ^ starting point
      -> (Vector Double, Matrix Double)  -- ^ solution vector and optimization path

nlFitting method epsabs epsrel maxit fun jac xinit = nlFitGen (fi (fromEnum method)) fun jac xinit epsabs epsrel maxit

nlFitGen m f jac xiv epsabs epsrel maxit = unsafePerformIO $ do
    let p   = dim xiv
        n   = dim (f xiv)
    fp <- mkVecVecfun (aux_vTov (checkdim1 n p . f))
    jp <- mkVecMatfun (aux_vTom (checkdim2 n p . jac))
    rawpath <- createMatrix RowMajor maxit (2+p)
    app2 (c_nlfit m fp jp epsabs epsrel (fi maxit) (fi n)) vec xiv mat rawpath "c_nlfit"
    let it = round (rawpath @@> (maxit-1,0))
        path = takeRows it rawpath
        [sol] = toRows $ dropRows (it-1) path
    freeHaskellFunPtr fp
    freeHaskellFunPtr jp
    return (subVector 2 p sol, path)

foreign import ccall safe "nlfit"
    c_nlfit:: CInt -> FunPtr TVV -> FunPtr TVM -> Double -> Double -> CInt -> CInt -> TVM

-------------------------------------------------------

checkdim1 n _p v
    | dim v == n = v
    | otherwise = error $ "Error: "++ show n
                        ++ " components expected in the result of the function supplied to nlFitting"

checkdim2 n p m
    | rows m == n && cols m == p = m
    | otherwise = error $ "Error: "++ show n ++ "x" ++ show p
                        ++ " Jacobian expected in nlFitting"

------------------------------------------------------------

err (model,deriv) dat vsol = zip sol errs where
    sol = toList vsol
    c = max 1 (chi/sqrt (fromIntegral dof))
    dof = length dat - (rows cov)
    chi = norm2 (fromList $ cost (resMs model) dat sol)
    js = fromLists $ jacobian (resDs deriv) dat sol
    cov = inv $ trans js <> js
    errs = toList $ scalar c * sqrt (takeDiag cov)



-- | Higher level interface to 'nlFitting' 'LevenbergMarquardtScaled'. The optimization function and
-- Jacobian are automatically built from a model f vs x = y and its derivatives, and a list of
-- instances (x, (y,sigma)) to be fitted.

fitModelScaled
         :: Double -- ^ absolute tolerance
         -> Double -- ^ relative tolerance
         -> Int    -- ^ maximum number of iterations allowed
         -> ([Double] -> x -> [Double], [Double] -> x -> [[Double]]) -- ^ (model, derivatives)
         -> [(x, ([Double], Double))] -- ^ instances
         -> [Double] -- ^ starting point
         -> ([(Double, Double)], Matrix Double) -- ^ (solution, error) and optimization path
fitModelScaled epsabs epsrel maxit (model,deriv) dt xin = (err (model,deriv) dt sol, path) where
    (sol,path) = nlFitting LevenbergMarquardtScaled epsabs epsrel maxit
                (fromList . cost (resMs model) dt . toList)
                (fromLists . jacobian (resDs deriv) dt . toList)
                (fromList xin)



-- | Higher level interface to 'nlFitting' 'LevenbergMarquardt'. The optimization function and
-- Jacobian are automatically built from a model f vs x = y and its derivatives, and a list of
-- instances (x,y) to be fitted.

fitModel :: Double -- ^ absolute tolerance
         -> Double -- ^ relative tolerance
         -> Int    -- ^ maximum number of iterations allowed
         -> ([Double] -> x -> [Double], [Double] -> x -> [[Double]]) -- ^ (model, derivatives)
         -> [(x, [Double])]  -- ^ instances
         -> [Double] -- ^ starting point
         -> ([Double], Matrix Double) -- ^ solution and optimization path
fitModel epsabs epsrel maxit (model,deriv) dt xin = (toList sol, path) where
    (sol,path) = nlFitting LevenbergMarquardt epsabs epsrel maxit
                (fromList . cost (resM model) dt . toList)
                (fromLists . jacobian (resD deriv) dt . toList)
                (fromList xin)

cost model ds vs = concatMap (model vs) ds

jacobian modelDer ds vs = concatMap (modelDer vs) ds

-- | Model-to-residual for association pairs with sigma, to be used with 'fitModel'.
resMs :: ([Double] -> x -> [Double]) -> [Double] -> (x, ([Double], Double)) -> [Double]
resMs m v = \(x,(ys,s)) -> zipWith (g s) (m v x) ys where g s a b = (a-b)/s

-- | Associated derivative for 'resMs'.
resDs :: ([Double] -> x -> [[Double]]) -> [Double] -> (x, ([Double], Double)) -> [[Double]]
resDs m v = \(x,(_,s)) -> map (map (/s)) (m v x)

-- | Model-to-residual for association pairs, to be used with 'fitModel'. It is equivalent
-- to 'resMs' with all sigmas = 1.
resM :: ([Double] -> x -> [Double]) -> [Double] -> (x, [Double]) -> [Double]
resM m v = \(x,ys) -> zipWith g (m v x) ys where g a b = a-b

-- | Associated derivative for 'resM'.
resD :: ([Double] -> x -> [[Double]]) -> [Double] -> (x, [Double]) -> [[Double]]
resD m v = \(x,_) -> m v x
