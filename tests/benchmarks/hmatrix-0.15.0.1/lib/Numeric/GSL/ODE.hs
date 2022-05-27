{- |
Module      :  Numeric.GSL.ODE
Copyright   :  (c) Alberto Ruiz 2010
License     :  GPL

Maintainer  :  Alberto Ruiz (aruiz at um dot es)
Stability   :  provisional
Portability :  uses ffi

Solution of ordinary differential equation (ODE) initial value problems.

<http://www.gnu.org/software/gsl/manual/html_node/Ordinary-Differential-Equations.html>

A simple example:

@import Numeric.GSL
import Numeric.LinearAlgebra
import Graphics.Plot

xdot t [x,v] = [v, -0.95*x - 0.1*v]

ts = linspace 100 (0,20 :: Double)

sol = odeSolve xdot [10,0] ts

main = mplot (ts : toColumns sol)@

-}
-----------------------------------------------------------------------------

module Numeric.GSL.ODE (
    odeSolve, odeSolveV, ODEMethod(..), Jacobian
) where

import Data.Packed.Internal
import Numeric.GSL.Internal

import Foreign.Ptr(FunPtr, nullFunPtr, freeHaskellFunPtr)
import Foreign.C.Types
import System.IO.Unsafe(unsafePerformIO)

-------------------------------------------------------------------------

type Jacobian = Double -> Vector Double -> Matrix Double

-- | Stepping functions
data ODEMethod = RK2 -- ^ Embedded Runge-Kutta (2, 3) method.
               | RK4 -- ^ 4th order (classical) Runge-Kutta. The error estimate is obtained by halving the step-size. For more efficient estimate of the error, use the embedded methods.
               | RKf45 -- ^ Embedded Runge-Kutta-Fehlberg (4, 5) method. This method is a good general-purpose integrator.
               | RKck -- ^ Embedded Runge-Kutta Cash-Karp (4, 5) method.
               | RK8pd -- ^ Embedded Runge-Kutta Prince-Dormand (8,9) method.
               | RK2imp Jacobian -- ^ Implicit 2nd order Runge-Kutta at Gaussian points.
               | RK4imp Jacobian -- ^ Implicit 4th order Runge-Kutta at Gaussian points.
               | BSimp Jacobian -- ^ Implicit Bulirsch-Stoer method of Bader and Deuflhard. The method is generally suitable for stiff problems.
               | RK1imp Jacobian -- ^ Implicit Gaussian first order Runge-Kutta. Also known as implicit Euler or backward Euler method. Error estimation is carried out by the step doubling method.
               | MSAdams -- ^ A variable-coefficient linear multistep Adams method in Nordsieck form. This stepper uses explicit Adams-Bashforth (predictor) and implicit Adams-Moulton (corrector) methods in P(EC)^m functional iteration mode. Method order varies dynamically between 1 and 12. 
               | MSBDF Jacobian -- ^ A variable-coefficient linear multistep backward differentiation formula (BDF) method in Nordsieck form. This stepper uses the explicit BDF formula as predictor and implicit BDF formula as corrector. A modified Newton iteration method is used to solve the system of non-linear equations. Method order varies dynamically between 1 and 5. The method is generally suitable for stiff problems.


-- | A version of 'odeSolveV' with reasonable default parameters and system of equations defined using lists.
odeSolve
    :: (Double -> [Double] -> [Double])        -- ^ xdot(t,x)
    -> [Double]        -- ^ initial conditions
    -> Vector Double   -- ^ desired solution times
    -> Matrix Double   -- ^ solution
odeSolve xdot xi ts = odeSolveV RKf45 hi epsAbs epsRel (l2v xdot) (fromList xi) ts
    where hi = (ts@>1 - ts@>0)/100
          epsAbs = 1.49012e-08
          epsRel = 1.49012e-08
          l2v f = \t -> fromList  . f t . toList

-- | Evolution of the system with adaptive step-size control.
odeSolveV
    :: ODEMethod
    -> Double -- ^ initial step size
    -> Double -- ^ absolute tolerance for the state vector
    -> Double -- ^ relative tolerance for the state vector
    -> (Double -> Vector Double -> Vector Double)   -- ^ xdot(t,x)
    -> Vector Double     -- ^ initial conditions
    -> Vector Double     -- ^ desired solution times
    -> Matrix Double     -- ^ solution
odeSolveV RK2 = odeSolveV' 0 Nothing
odeSolveV RK4 = odeSolveV' 1 Nothing
odeSolveV RKf45 = odeSolveV' 2 Nothing
odeSolveV RKck = odeSolveV' 3 Nothing
odeSolveV RK8pd = odeSolveV' 4 Nothing
odeSolveV (RK2imp jac) = odeSolveV' 5 (Just jac)
odeSolveV (RK4imp jac) = odeSolveV' 6 (Just jac)
odeSolveV (BSimp jac) = odeSolveV' 7 (Just jac)
odeSolveV (RK1imp jac) = odeSolveV' 8 (Just jac)
odeSolveV MSAdams = odeSolveV' 9 Nothing
odeSolveV (MSBDF jac) = odeSolveV' 10 (Just jac)


odeSolveV'
    :: CInt
    -> Maybe (Double -> Vector Double -> Matrix Double)   -- ^ optional jacobian
    -> Double -- ^ initial step size
    -> Double -- ^ absolute tolerance for the state vector
    -> Double -- ^ relative tolerance for the state vector
    -> (Double -> Vector Double -> Vector Double)   -- ^ xdot(t,x)
    -> Vector Double     -- ^ initial conditions
    -> Vector Double     -- ^ desired solution times
    -> Matrix Double     -- ^ solution
odeSolveV' method mbjac h epsAbs epsRel f  xiv ts = unsafePerformIO $ do
    let n   = dim xiv
    fp <- mkDoubleVecVecfun (\t -> aux_vTov (checkdim1 n . f t))
    jp <- case mbjac of
        Just jac -> mkDoubleVecMatfun (\t -> aux_vTom (checkdim2 n . jac t))
        Nothing  -> return nullFunPtr
    sol <- vec xiv $ \xiv' ->
            vec (checkTimes ts) $ \ts' ->
             createMIO (dim ts) n
              (ode_c (method) h epsAbs epsRel fp jp // xiv' // ts' )
              "ode"
    freeHaskellFunPtr fp
    return sol

foreign import ccall safe "ode"
    ode_c :: CInt -> Double -> Double -> Double -> FunPtr (Double -> TVV) -> FunPtr (Double -> TVM) -> TVVM

-------------------------------------------------------

checkdim1 n v
    | dim v == n = v
    | otherwise = error $ "Error: "++ show n
                        ++ " components expected in the result of the function supplied to odeSolve"

checkdim2 n m
    | rows m == n && cols m == n = m
    | otherwise = error $ "Error: "++ show n ++ "x" ++ show n
                        ++ " Jacobian expected in odeSolve"

checkTimes ts | dim ts > 1 && all (>0) (zipWith subtract ts' (tail ts')) = ts
              | otherwise = error "odeSolve requires increasing times"
    where ts' = toList ts
