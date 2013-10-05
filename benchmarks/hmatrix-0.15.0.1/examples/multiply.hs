{-# LANGUAGE UnicodeSyntax
           , MultiParamTypeClasses
           , FunctionalDependencies
           , FlexibleInstances
           , FlexibleContexts
--           , OverlappingInstances
           , UndecidableInstances #-}

import Numeric.LinearAlgebra

class Scaling a b c | a b -> c where
 -- ^ 0x22C5	8901	DOT OPERATOR, scaling
 infixl 7 ⋅
 (⋅) :: a -> b -> c

class Contraction a b c | a b -> c where
 -- ^ 0x00D7	215	MULTIPLICATION SIGN	×, contraction
 infixl 7 ×
 (×) :: a -> b -> c

class Outer a b c | a b -> c where
 -- ^ 0x2297	8855	CIRCLED TIMES	⊗, outer product (not associative)
 infixl 7 ⊗
 (⊗) :: a -> b -> c


-------

instance (Num t) => Scaling t t t where
    (⋅) = (*)

instance Container Vector t => Scaling t (Vector t) (Vector t) where
    (⋅) = scale

instance Container Vector t => Scaling (Vector t) t (Vector t) where
    (⋅) = flip scale

instance Container Vector t => Scaling t (Matrix t) (Matrix t) where
    (⋅) = scale

instance Container Vector t => Scaling (Matrix t) t (Matrix t) where
    (⋅) = flip scale


instance Product t => Contraction (Vector t) (Vector t) t where
    (×) = dot

instance Product t => Contraction (Matrix t) (Vector t) (Vector t) where
    (×) = mXv

instance Product t => Contraction (Vector t) (Matrix t) (Vector t) where
    (×) = vXm

instance Product t => Contraction (Matrix t) (Matrix t) (Matrix t) where
    (×) = mXm


--instance Scaling a b c => Contraction a b c where
--    (×) = (⋅)

-----

instance Product t => Outer (Vector t) (Vector t) (Matrix t) where
    (⊗) = outer

instance Product t => Outer (Vector t) (Matrix t) (Matrix t) where
    v ⊗ m = kronecker (asColumn v) m

instance Product t => Outer (Matrix t) (Vector t) (Matrix t) where
    m ⊗ v = kronecker m (asRow v)

instance Product t => Outer (Matrix t) (Matrix t) (Matrix t) where
    (⊗) = kronecker

-----


v = 3 |> [1..] :: Vector Double

m = (3 >< 3) [1..] :: Matrix Double

s = 3 :: Double

a = s ⋅ v × m × m × v ⋅ s

b = (v ⊗ m) ⊗ (v ⊗ m)

c = v ⊗ m ⊗ v ⊗ m

d = s ⋅ (3 |> [10,20..] :: Vector Double)

main = do
    print $ scale s v <> m <.> v 
    print $ scale s v <.> (m <> v)
    print $ s * (v <> m <.> v)
    print $ s ⋅ v × m × v
    print a
    print (b == c)
    print d

