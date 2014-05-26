{-# LANGUAGE TypeSynonymInstances #-}

module Means where

import Prelude hiding ((*))
import qualified Prelude as Pr
import Language.Haskell.Liquid.Prelude

type Scalar = Double

{-@ assume (*) :: x:Scalar -> y:Scalar -> {v:Scalar | v = (times x y)} @-}
(*) :: Scalar -> Scalar -> Scalar
(*) = (Pr.*)

{-@ assume inverse :: x:{v:Scalar | v != 0} -> {v:Scalar | v = (inverse x)} @-}
inverse :: Scalar -> Scalar
inverse x | x == zero = error "inverse a zero value"
          | otherwise = one / x

-- Double 1 does not take a singleton type
{-@ assume one :: {v:Scalar | v = 1} @-}
one :: Scalar
one = 1

{-@ assume two :: {v:Scalar | v = 2} @-}
two :: Scalar
two = 2

{-@ assume zero :: {v:Scalar | v = 0} @-}
zero :: Scalar
zero = 0


{-@
  measure times :: Scalar -> Scalar -> Scalar
  @-}

{-@
  measure inverse :: Scalar -> Scalar
  @-}

-- Properties of multiplication

{-@ mulNeutral :: x:Scalar -> {v:Bool | x = (times 1 x)} @-}
mulNeutral :: Scalar -> Bool
mulNeutral x | x == one * x = True
      --        | otherwise  = error "mulNeutral fails"

{-@ mulExpTwo :: x:Scalar -> {v:Bool | (times 2 x) = x + x } @-}
mulExpTwo :: Scalar -> Bool
mulExpTwo x  | two * x == x + x = True
      --        | otherwise  = error "mulAssoc fails"

{-@ mulTrans :: x:Scalar -> y:Scalar -> z:Scalar -> {v:Bool | (times (times x y) z) = (times x (times y z))} @-}
mulTrans :: Scalar -> Scalar -> Scalar -> Bool
mulTrans x y z | x * y * z == x * (y * z) = True
      --        | otherwise  = error "mulAssoc fails"

{-@ mulAssoc :: x:Scalar -> y:Scalar -> {v:Bool | (times x y) = (times y x)} @-}
mulAssoc :: Scalar -> Scalar -> Bool
mulAssoc x y | x * y == y * x = True
      --        | otherwise  = error "mulAssoc fails"

{-@ mulDivId :: x:{v:Scalar|v/= 0} -> {v:Bool | 1 = (times x (inverse x))} @-}
mulDivId :: Scalar -> Bool
mulDivId x | one == x * inverse x = True
      --   | otherwise  = error "mulDivId fails"

-- Class Specifications
class Vec a where
  norm :: a -> Scalar
  mean :: a -> a -> Scalar
  {-@ dist :: Vec a => x:a -> y:a -> {v:Scalar | v = (dist x y) } @-}
  dist :: a -> a -> Scalar

{-@ class measure dist :: forall a . a -> a -> Scalar @-}

-- Assumptions:
-- Triangle Inequality

{-@ triangleInequality :: Vec a => x:a -> y:a -> c:a ->
      {v:Bool | ((((dist x c) + (dist c y)) >= (dist x y)))} @-}
triangleInequality :: Vec a => a -> a -> a -> Bool
triangleInequality x y c 
  | (dist x c + dist c y) >= (dist x y) 
  = True
  | otherwise                           
  = error "Vec.dist does not satisfy triangleInequality"            



{-@ foo :: x:Scalar -> {v:Scalar |  v= x} @-}
foo :: Scalar -> Scalar
foo x = liquidAssume (mulNeutral x) $ one * x 


{-@ type Valid = {v:Bool | ((Prop v) <=> true)} @-}

{-@ prop1 :: Vec a => a -> a -> a -> Valid @-}
prop1 :: Vec a => a -> a -> a -> Bool
prop1 x y c = liquidAssume ( triangleInequality x y c 
                          && mulNeutral dxy 
                          && mulDivId two
                          && mulTrans two itwo dxy
                          && mulExpTwo itwo_dxy
                           ) $ 
              (dist x c) + (dist c y) >= (itwo_dxy + itwo_dxy')
  where c'  = mean x y
        dxy = dist x y
        itwo = inverse two
        itwo_dxy = itwo * dxy
        itwo_dxy' = inverse two * dist x y 
