-----------------------------------------------------------------------------
{- |
Module      :  Numeric.LinearAlgebra
Copyright   :  (c) Alberto Ruiz 2006-10
License     :  GPL-style

Maintainer  :  Alberto Ruiz (aruiz at um dot es)
Stability   :  provisional
Portability :  uses ffi

This module reexports all normally required functions for Linear Algebra applications.

It also provides instances of standard classes 'Show', 'Read', 'Eq',
'Num', 'Fractional', and 'Floating' for 'Vector' and 'Matrix'.
In arithmetic operations one-component vectors and matrices automatically
expand to match the dimensions of the other operand.

-}
-----------------------------------------------------------------------------
module Numeric.LinearAlgebra (
    module Numeric.Container,
    module Numeric.LinearAlgebra.Algorithms
) where

import Numeric.Container
import Numeric.LinearAlgebra.Algorithms
import Numeric.Matrix()
import Numeric.Vector()