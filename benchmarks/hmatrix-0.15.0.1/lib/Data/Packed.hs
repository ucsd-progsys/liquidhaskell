-----------------------------------------------------------------------------
{- |
Module      :  Data.Packed
Copyright   :  (c) Alberto Ruiz 2006-2010
License     :  GPL-style

Maintainer  :  Alberto Ruiz (aruiz at um dot es)
Stability   :  provisional
Portability :  uses ffi

Types for dense 'Vector' and 'Matrix' of 'Storable' elements.

-}
-----------------------------------------------------------------------------

module Data.Packed (
    module Data.Packed.Vector,
    module Data.Packed.Matrix,
--    module Numeric.Conversion,
--    module Data.Packed.Random,
--    module Data.Complex
) where

import Data.Packed.Vector
import Data.Packed.Matrix
--import Data.Packed.Random
--import Data.Complex
--import Numeric.Conversion