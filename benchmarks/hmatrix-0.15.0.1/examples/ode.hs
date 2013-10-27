{-# LANGUAGE ViewPatterns #-}
import Numeric.GSL.ODE
import Numeric.LinearAlgebra
import Graphics.Plot
import Debug.Trace(trace)
debug x = trace (show x) x

vanderpol mu = do
    let xdot mu t [x,v] = [v, -x + mu * v * (1-x^2)]
        ts = linspace 1000 (0,50)
        sol = toColumns $ odeSolve (xdot mu) [1,0] ts
    mplot (ts : sol)
    mplot sol


harmonic w d = do
    let xdot w d t [x,v] = [v, a*x + b*v] where a = -w^2; b = -2*d*w
        ts = linspace 100 (0,20)
        sol = odeSolve (xdot w d) [1,0] ts
    mplot (ts : toColumns sol)


kepler v a = mplot (take 2 $ toColumns sol) where
    xdot t [x,y,vx,vy] = [vx,vy,x*k,y*k]
        where g=1
              k=(-g)*(x*x+y*y)**(-1.5)
    ts = linspace 100 (0,30)
    sol = odeSolve xdot [4, 0, v * cos (a*degree), v * sin (a*degree)] ts
    degree = pi/180


main = do
    vanderpol 2
    harmonic 1 0
    harmonic 1 0.1
    kepler 0.3 60
    kepler 0.4 70
    vanderpol' 2

-- example of odeSolveV with jacobian
vanderpol' mu = do
    let xdot mu t (toList->[x,v]) = fromList [v, -x + mu * v * (1-x^2)]
        jac t (toList->[x,v]) = (2><2) [ 0          ,          1
                                       , -1-2*x*v*mu, mu*(1-x**2) ]
        ts = linspace 1000 (0,50)
        hi = (ts@>1 - ts@>0)/100
        sol = toColumns $ odeSolveV (MSBDF jac) hi 1E-8 1E-8 (xdot mu) (fromList [1,0]) ts
    mplot sol


