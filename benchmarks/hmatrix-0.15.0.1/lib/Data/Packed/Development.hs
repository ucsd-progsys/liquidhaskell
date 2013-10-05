
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Packed.Development
-- Copyright   :  (c) Alberto Ruiz 2009
-- License     :  GPL
--
-- Maintainer  :  Alberto Ruiz <aruiz@um.es>
-- Stability   :  provisional
-- Portability :  portable
--
-- The library can be easily extended with additional foreign functions
-- using the tools in this module. Illustrative usage examples can be found
-- in the @examples\/devel@ folder included in the package.
--
-----------------------------------------------------------------------------

module Data.Packed.Development (
    createVector, createMatrix,
    vec, mat,
    app1, app2, app3, app4,
    app5, app6, app7, app8, app9, app10,
    MatrixOrder(..), orderOf, cmat, fmat,
    unsafeFromForeignPtr,
    unsafeToForeignPtr,
    check, (//),
    at', atM'
) where

import Data.Packed.Internal
