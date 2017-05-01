{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Numeric.Vector
-- Copyright   :  (c) Alberto Ruiz 2011
-- License     :  GPL-style
--
-- Maintainer  :  Alberto Ruiz <aruiz@um.es>
-- Stability   :  provisional
-- Portability :  portable
--
-- Provides instances of standard classes 'Show', 'Read', 'Eq',
-- 'Num', 'Fractional',  and 'Floating' for 'Vector'.
-- 
-----------------------------------------------------------------------------

module Numeric.Vector () where

import Numeric.GSL.Vector
import Numeric.Container

-------------------------------------------------------------------

adaptScalar f1 f2 f3 x y
    | dim x == 1 = f1   (x@>0) y
    | dim y == 1 = f3 x (y@>0)
    | otherwise = f2 x y

------------------------------------------------------------------

instance Num (Vector Float) where
    (+) = adaptScalar addConstant add (flip addConstant)
    negate = scale (-1)
    (*) = adaptScalar scale mul (flip scale)
    signum = vectorMapF Sign
    abs = vectorMapF Abs
    fromInteger = fromList . return . fromInteger

instance Num (Vector Double) where
    (+) = adaptScalar addConstant add (flip addConstant)
    negate = scale (-1)
    (*) = adaptScalar scale mul (flip scale)
    signum = vectorMapR Sign
    abs = vectorMapR Abs
    fromInteger = fromList . return . fromInteger

instance Num (Vector (Complex Double)) where
    (+) = adaptScalar addConstant add (flip addConstant)
    negate = scale (-1)
    (*) = adaptScalar scale mul (flip scale)
    signum = vectorMapC Sign
    abs = vectorMapC Abs
    fromInteger = fromList . return . fromInteger

instance Num (Vector (Complex Float)) where
    (+) = adaptScalar addConstant add (flip addConstant)
    negate = scale (-1)
    (*) = adaptScalar scale mul (flip scale)
    signum = vectorMapQ Sign
    abs = vectorMapQ Abs
    fromInteger = fromList . return . fromInteger

---------------------------------------------------

instance (Container Vector a, Num (Vector a)) => Fractional (Vector a) where
    fromRational n = fromList [fromRational n]
    (/) = adaptScalar f divide g where
        r `f` v = scaleRecip r v
        v `g` r = scale (recip r) v

-------------------------------------------------------

instance Floating (Vector Float) where
    sin   = vectorMapF Sin
    cos   = vectorMapF Cos
    tan   = vectorMapF Tan
    asin  = vectorMapF ASin
    acos  = vectorMapF ACos
    atan  = vectorMapF ATan
    sinh  = vectorMapF Sinh
    cosh  = vectorMapF Cosh
    tanh  = vectorMapF Tanh
    asinh = vectorMapF ASinh
    acosh = vectorMapF ACosh
    atanh = vectorMapF ATanh
    exp   = vectorMapF Exp
    log   = vectorMapF Log
    sqrt  = vectorMapF Sqrt
    (**)  = adaptScalar (vectorMapValF PowSV) (vectorZipF Pow) (flip (vectorMapValF PowVS))
    pi    = fromList [pi]

-------------------------------------------------------------

instance Floating (Vector Double) where
    sin   = vectorMapR Sin
    cos   = vectorMapR Cos
    tan   = vectorMapR Tan
    asin  = vectorMapR ASin
    acos  = vectorMapR ACos
    atan  = vectorMapR ATan
    sinh  = vectorMapR Sinh
    cosh  = vectorMapR Cosh
    tanh  = vectorMapR Tanh
    asinh = vectorMapR ASinh
    acosh = vectorMapR ACosh
    atanh = vectorMapR ATanh
    exp   = vectorMapR Exp
    log   = vectorMapR Log
    sqrt  = vectorMapR Sqrt
    (**)  = adaptScalar (vectorMapValR PowSV) (vectorZipR Pow) (flip (vectorMapValR PowVS))
    pi    = fromList [pi]

-------------------------------------------------------------

instance Floating (Vector (Complex Double)) where
    sin   = vectorMapC Sin
    cos   = vectorMapC Cos
    tan   = vectorMapC Tan
    asin  = vectorMapC ASin
    acos  = vectorMapC ACos
    atan  = vectorMapC ATan
    sinh  = vectorMapC Sinh
    cosh  = vectorMapC Cosh
    tanh  = vectorMapC Tanh
    asinh = vectorMapC ASinh
    acosh = vectorMapC ACosh
    atanh = vectorMapC ATanh
    exp   = vectorMapC Exp
    log   = vectorMapC Log
    sqrt  = vectorMapC Sqrt
    (**)  = adaptScalar (vectorMapValC PowSV) (vectorZipC Pow) (flip (vectorMapValC PowVS))
    pi    = fromList [pi]

-----------------------------------------------------------

instance Floating (Vector (Complex Float)) where
    sin   = vectorMapQ Sin
    cos   = vectorMapQ Cos
    tan   = vectorMapQ Tan
    asin  = vectorMapQ ASin
    acos  = vectorMapQ ACos
    atan  = vectorMapQ ATan
    sinh  = vectorMapQ Sinh
    cosh  = vectorMapQ Cosh
    tanh  = vectorMapQ Tanh
    asinh = vectorMapQ ASinh
    acosh = vectorMapQ ACosh
    atanh = vectorMapQ ATanh
    exp   = vectorMapQ Exp
    log   = vectorMapQ Log
    sqrt  = vectorMapQ Sqrt
    (**)  = adaptScalar (vectorMapValQ PowSV) (vectorZipQ Pow) (flip (vectorMapValQ PowVS))
    pi    = fromList [pi]

