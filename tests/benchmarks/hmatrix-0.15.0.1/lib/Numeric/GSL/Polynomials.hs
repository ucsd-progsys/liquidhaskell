{-# LANGUAGE CPP, ForeignFunctionInterface #-}
-----------------------------------------------------------------------------
{- |
Module      :  Numeric.GSL.Polynomials
Copyright   :  (c) Alberto Ruiz 2006
License     :  GPL-style

Maintainer  :  Alberto Ruiz (aruiz at um dot es)
Stability   :  provisional
Portability :  uses ffi

Polynomials.

<http://www.gnu.org/software/gsl/manual/html_node/General-Polynomial-Equations.html#General-Polynomial-Equations>

-}
-----------------------------------------------------------------------------
module Numeric.GSL.Polynomials (
    polySolve
) where

import Data.Packed.Internal
import Data.Complex
import System.IO.Unsafe (unsafePerformIO)

#if __GLASGOW_HASKELL__ >= 704
import Foreign.C.Types (CInt(..))
#endif

{- | Solution of general polynomial equations, using /gsl_poly_complex_solve/. For example,
     the three solutions of x^3 + 8 = 0

@\> polySolve [8,0,0,1]
[(-1.9999999999999998) :+ 0.0,
 1.0 :+ 1.732050807568877,
 1.0 :+ (-1.732050807568877)]@

The example in the GSL manual: To find the roots of x^5 -1 = 0:

@\> polySolve [-1, 0, 0, 0, 0, 1]
[(-0.8090169943749475) :+ 0.5877852522924731,
(-0.8090169943749475) :+ (-0.5877852522924731),
0.30901699437494734 :+ 0.9510565162951536,
0.30901699437494734 :+ (-0.9510565162951536),
1.0 :+ 0.0]@

-}  
polySolve :: [Double] -> [Complex Double]
polySolve = toList . polySolve' . fromList

polySolve' :: Vector Double -> Vector (Complex Double)
polySolve' v | dim v > 1 = unsafePerformIO $ do
    r <- createVector (dim v-1)
    app2 c_polySolve vec v vec r "polySolve"
    return r
             | otherwise = error "polySolve on a polynomial of degree zero"

foreign import ccall unsafe "gsl-aux.h polySolve" c_polySolve:: TVCV
