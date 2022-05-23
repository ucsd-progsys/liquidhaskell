{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Numeric.ContainerBoot
-- Copyright   :  (c) Alberto Ruiz 2010
-- License     :  GPL-style
--
-- Maintainer  :  Alberto Ruiz <aruiz@um.es>
-- Stability   :  provisional
-- Portability :  portable
--
-- Module to avoid cyclyc dependencies.
--
-----------------------------------------------------------------------------

module Numeric.ContainerBoot (
    -- * Basic functions
    ident, diag, ctrans,
    -- * Generic operations
    Container(..),
    -- * Matrix product and related functions
    Product(..),
    mXm,mXv,vXm,
    outer, kronecker,
    -- * Element conversion
    Convert(..),
    Complexable(),
    RealElement(),

    RealOf, ComplexOf, SingleOf, DoubleOf,

    IndexOf,
    module Data.Complex,
    -- * Experimental
    build', konst'
) where

import Data.Packed
import Data.Packed.ST as ST
import Numeric.Conversion
import Data.Packed.Internal
import Numeric.GSL.Vector
import Data.Complex
import Control.Monad(ap)

import Numeric.LinearAlgebra.LAPACK(multiplyR,multiplyC,multiplyF,multiplyQ)

-------------------------------------------------------------------

type family IndexOf (c :: * -> *)

type instance IndexOf Vector = Int
type instance IndexOf Matrix = (Int,Int)

type family ArgOf (c :: * -> *) a

type instance ArgOf Vector a = a -> a
type instance ArgOf Matrix a = a -> a -> a

-------------------------------------------------------------------

-- | Basic element-by-element functions for numeric containers
class (Complexable c, Fractional e, Element e) => Container c e where
    -- | create a structure with a single element
    scalar      :: e -> c e
    -- | complex conjugate
    conj        :: c e -> c e
    scale       :: e -> c e -> c e
    -- | scale the element by element reciprocal of the object:
    --
    -- @scaleRecip 2 (fromList [5,i]) == 2 |> [0.4 :+ 0.0,0.0 :+ (-2.0)]@
    scaleRecip  :: e -> c e -> c e
    addConstant :: e -> c e -> c e
    add         :: c e -> c e -> c e
    sub         :: c e -> c e -> c e
    -- | element by element multiplication
    mul         :: c e -> c e -> c e
    -- | element by element division
    divide      :: c e -> c e -> c e
    equal       :: c e -> c e -> Bool
    --
    -- element by element inverse tangent
    arctan2     :: c e -> c e -> c e
    --
    -- | cannot implement instance Functor because of Element class constraint
    cmap        :: (Element b) => (e -> b) -> c e -> c b
    -- | constant structure of given size
    konst       :: e -> IndexOf c -> c e
    -- | create a structure using a function
    --
    -- Hilbert matrix of order N:
    --
    -- @hilb n = build (n,n) (\\i j -> 1/(i+j+1))@
    build       :: IndexOf c -> (ArgOf c e) -> c e
    --build       :: BoundsOf f -> f -> (ContainerOf f) e
    --
    -- | indexing function
    atIndex     :: c e -> IndexOf c -> e
    -- | index of min element
    minIndex    :: c e -> IndexOf c
    -- | index of max element
    maxIndex    :: c e -> IndexOf c
    -- | value of min element
    minElement  :: c e -> e
    -- | value of max element
    maxElement  :: c e -> e
    -- the C functions sumX/prodX are twice as fast as using foldVector
    -- | the sum of elements (faster than using @fold@)
    sumElements :: c e -> e
    -- | the product of elements (faster than using @fold@)
    prodElements :: c e -> e

    -- | A more efficient implementation of @cmap (\\x -> if x>0 then 1 else 0)@
    --
    -- @> step $ linspace 5 (-1,1::Double)
    -- 5 |> [0.0,0.0,0.0,1.0,1.0]@
    
    step :: RealElement e => c e -> c e

    -- | Element by element version of @case compare a b of {LT -> l; EQ -> e; GT -> g}@.
    --
    -- Arguments with any dimension = 1 are automatically expanded: 
    --
    -- @> cond ((1>\<4)[1..]) ((3>\<1)[1..]) 0 100 ((3>\<4)[1..]) :: Matrix Double
    -- (3><4)
    -- [ 100.0,   2.0,   3.0,  4.0
    -- ,   0.0, 100.0,   7.0,  8.0
    -- ,   0.0,   0.0, 100.0, 12.0 ]@
    
    cond :: RealElement e 
         => c e -- ^ a
         -> c e -- ^ b
         -> c e -- ^ l 
         -> c e -- ^ e
         -> c e -- ^ g
         -> c e -- ^ result

    -- | Find index of elements which satisfy a predicate
    --
    -- @> find (>0) (ident 3 :: Matrix Double)
    -- [(0,0),(1,1),(2,2)]@

    find :: (e -> Bool) -> c e -> [IndexOf c]

    -- | Create a structure from an association list
    --
    -- @> assoc 5 0 [(2,7),(1,3)] :: Vector Double
    -- 5 |> [0.0,3.0,7.0,0.0,0.0]@
    
    assoc :: IndexOf c        -- ^ size
          -> e                -- ^ default value
          -> [(IndexOf c, e)] -- ^ association list
          -> c e              -- ^ result

    -- | Modify a structure using an update function
    --
    -- @> accum (ident 5) (+) [((1,1),5),((0,3),3)] :: Matrix Double
    -- (5><5)
    --  [ 1.0, 0.0, 0.0, 3.0, 0.0
    --  , 0.0, 6.0, 0.0, 0.0, 0.0
    --  , 0.0, 0.0, 1.0, 0.0, 0.0
    --  , 0.0, 0.0, 0.0, 1.0, 0.0
    --  , 0.0, 0.0, 0.0, 0.0, 1.0 ]@
    
    accum :: c e              -- ^ initial structure
          -> (e -> e -> e)    -- ^ update function
          -> [(IndexOf c, e)] -- ^ association list
          -> c e              -- ^ result

--------------------------------------------------------------------------

instance Container Vector Float where
    scale = vectorMapValF Scale
    scaleRecip = vectorMapValF Recip
    addConstant = vectorMapValF AddConstant
    add = vectorZipF Add
    sub = vectorZipF Sub
    mul = vectorZipF Mul
    divide = vectorZipF Div
    equal u v = dim u == dim v && maxElement (vectorMapF Abs (sub u v)) == 0.0
    arctan2 = vectorZipF ATan2
    scalar x = fromList [x]
    konst = constantD
    build = buildV
    conj = id
    cmap = mapVector
    atIndex = (@>)
    minIndex     = round . toScalarF MinIdx
    maxIndex     = round . toScalarF MaxIdx
    minElement  = toScalarF Min
    maxElement  = toScalarF Max
    sumElements  = sumF
    prodElements = prodF
    step = stepF
    find = findV
    assoc = assocV
    accum = accumV
    cond = condV condF

instance Container Vector Double where
    scale = vectorMapValR Scale
    scaleRecip = vectorMapValR Recip
    addConstant = vectorMapValR AddConstant
    add = vectorZipR Add
    sub = vectorZipR Sub
    mul = vectorZipR Mul
    divide = vectorZipR Div
    equal u v = dim u == dim v && maxElement (vectorMapR Abs (sub u v)) == 0.0
    arctan2 = vectorZipR ATan2
    scalar x = fromList [x]
    konst = constantD
    build = buildV
    conj = id
    cmap = mapVector
    atIndex = (@>)
    minIndex     = round . toScalarR MinIdx
    maxIndex     = round . toScalarR MaxIdx
    minElement  = toScalarR Min
    maxElement  = toScalarR Max
    sumElements  = sumR
    prodElements = prodR
    step = stepD
    find = findV
    assoc = assocV
    accum = accumV
    cond = condV condD

instance Container Vector (Complex Double) where
    scale = vectorMapValC Scale
    scaleRecip = vectorMapValC Recip
    addConstant = vectorMapValC AddConstant
    add = vectorZipC Add
    sub = vectorZipC Sub
    mul = vectorZipC Mul
    divide = vectorZipC Div
    equal u v = dim u == dim v && maxElement (mapVector magnitude (sub u v)) == 0.0
    arctan2 = vectorZipC ATan2
    scalar x = fromList [x]
    konst = constantD
    build = buildV
    conj = conjugateC
    cmap = mapVector
    atIndex = (@>)
    minIndex     = minIndex . fst . fromComplex . (zipVectorWith (*) `ap` mapVector conjugate)
    maxIndex     = maxIndex . fst . fromComplex . (zipVectorWith (*) `ap` mapVector conjugate)
    minElement  = ap (@>) minIndex
    maxElement  = ap (@>) maxIndex
    sumElements  = sumC
    prodElements = prodC
    step = undefined -- cannot match
    find = findV
    assoc = assocV
    accum = accumV
    cond = undefined -- cannot match

instance Container Vector (Complex Float) where
    scale = vectorMapValQ Scale
    scaleRecip = vectorMapValQ Recip
    addConstant = vectorMapValQ AddConstant
    add = vectorZipQ Add
    sub = vectorZipQ Sub
    mul = vectorZipQ Mul
    divide = vectorZipQ Div
    equal u v = dim u == dim v && maxElement (mapVector magnitude (sub u v)) == 0.0
    arctan2 = vectorZipQ ATan2
    scalar x = fromList [x]
    konst = constantD
    build = buildV
    conj = conjugateQ
    cmap = mapVector
    atIndex = (@>)
    minIndex     = minIndex . fst . fromComplex . (zipVectorWith (*) `ap` mapVector conjugate)
    maxIndex     = maxIndex . fst . fromComplex . (zipVectorWith (*) `ap` mapVector conjugate)
    minElement  = ap (@>) minIndex
    maxElement  = ap (@>) maxIndex
    sumElements  = sumQ
    prodElements = prodQ
    step = undefined -- cannot match
    find = findV
    assoc = assocV
    accum = accumV
    cond = undefined -- cannot match

---------------------------------------------------------------

instance (Container Vector a) => Container Matrix a where
    scale x = liftMatrix (scale x)
    scaleRecip x = liftMatrix (scaleRecip x)
    addConstant x = liftMatrix (addConstant x)
    add = liftMatrix2 add
    sub = liftMatrix2 sub
    mul = liftMatrix2 mul
    divide = liftMatrix2 divide
    equal a b = cols a == cols b && flatten a `equal` flatten b
    arctan2 = liftMatrix2 arctan2
    scalar x = (1><1) [x]
    konst v (r,c) = reshape c (konst v (r*c))
    build = buildM
    conj = liftMatrix conj
    cmap f = liftMatrix (mapVector f)
    atIndex = (@@>)
    minIndex m = let (r,c) = (rows m,cols m)
                     i = (minIndex $ flatten m)
                 in (i `div` c,i `mod` c)
    maxIndex m = let (r,c) = (rows m,cols m)
                     i = (maxIndex $ flatten m)
                 in (i `div` c,i `mod` c)
    minElement = ap (@@>) minIndex
    maxElement = ap (@@>) maxIndex
    sumElements = sumElements . flatten
    prodElements = prodElements . flatten
    step = liftMatrix step
    find = findM
    assoc = assocM
    accum = accumM
    cond = condM

----------------------------------------------------

-- | Matrix product and related functions
class Element e => Product e where
    -- | matrix product
    multiply :: Matrix e -> Matrix e -> Matrix e
    -- | dot (inner) product
    dot        :: Vector e -> Vector e -> e
    -- | sum of absolute value of elements (differs in complex case from @norm1@)
    absSum     :: Vector e -> RealOf e
    -- | sum of absolute value of elements
    norm1      :: Vector e -> RealOf e
    -- | euclidean norm
    norm2      :: Vector e -> RealOf e
    -- | element of maximum magnitude
    normInf    :: Vector e -> RealOf e

instance Product Float where
    norm2      = toScalarF Norm2
    absSum     = toScalarF AbsSum
    dot        = dotF
    norm1      = toScalarF AbsSum
    normInf    = maxElement . vectorMapF Abs
    multiply = multiplyF

instance Product Double where
    norm2      = toScalarR Norm2
    absSum     = toScalarR AbsSum
    dot        = dotR
    norm1      = toScalarR AbsSum
    normInf    = maxElement . vectorMapR Abs
    multiply = multiplyR

instance Product (Complex Float) where
    norm2      = toScalarQ Norm2
    absSum     = toScalarQ AbsSum
    dot        = dotQ
    norm1      = sumElements . fst . fromComplex . vectorMapQ Abs
    normInf    = maxElement . fst . fromComplex . vectorMapQ Abs
    multiply = multiplyQ

instance Product (Complex Double) where
    norm2      = toScalarC Norm2
    absSum     = toScalarC AbsSum
    dot        = dotC
    norm1      = sumElements . fst . fromComplex . vectorMapC Abs
    normInf    = maxElement . fst . fromComplex . vectorMapC Abs
    multiply = multiplyC

----------------------------------------------------------

-- synonym for matrix product
mXm :: Product t => Matrix t -> Matrix t -> Matrix t
mXm = multiply

-- matrix - vector product
mXv :: Product t => Matrix t -> Vector t -> Vector t
mXv m v = flatten $ m `mXm` (asColumn v)

-- vector - matrix product
vXm :: Product t => Vector t -> Matrix t -> Vector t
vXm v m = flatten $ (asRow v) `mXm` m

{- | Outer product of two vectors.

@\> 'fromList' [1,2,3] \`outer\` 'fromList' [5,2,3]
(3><3)
 [  5.0, 2.0, 3.0
 , 10.0, 4.0, 6.0
 , 15.0, 6.0, 9.0 ]@
-}
outer :: (Product t) => Vector t -> Vector t -> Matrix t
outer u v = asColumn u `multiply` asRow v

{- | Kronecker product of two matrices.

@m1=(2><3)
 [ 1.0,  2.0, 0.0
 , 0.0, -1.0, 3.0 ]
m2=(4><3)
 [  1.0,  2.0,  3.0
 ,  4.0,  5.0,  6.0
 ,  7.0,  8.0,  9.0
 , 10.0, 11.0, 12.0 ]@

@\> kronecker m1 m2
(8><9)
 [  1.0,  2.0,  3.0,   2.0,   4.0,   6.0,  0.0,  0.0,  0.0
 ,  4.0,  5.0,  6.0,   8.0,  10.0,  12.0,  0.0,  0.0,  0.0
 ,  7.0,  8.0,  9.0,  14.0,  16.0,  18.0,  0.0,  0.0,  0.0
 , 10.0, 11.0, 12.0,  20.0,  22.0,  24.0,  0.0,  0.0,  0.0
 ,  0.0,  0.0,  0.0,  -1.0,  -2.0,  -3.0,  3.0,  6.0,  9.0
 ,  0.0,  0.0,  0.0,  -4.0,  -5.0,  -6.0, 12.0, 15.0, 18.0
 ,  0.0,  0.0,  0.0,  -7.0,  -8.0,  -9.0, 21.0, 24.0, 27.0
 ,  0.0,  0.0,  0.0, -10.0, -11.0, -12.0, 30.0, 33.0, 36.0 ]@
-}
kronecker :: (Product t) => Matrix t -> Matrix t -> Matrix t
kronecker a b = fromBlocks
              . splitEvery (cols a)
              . map (reshape (cols b))
              . toRows
              $ flatten a `outer` flatten b

-------------------------------------------------------------------


class Convert t where
    real    :: Container c t => c (RealOf t) -> c t
    complex :: Container c t => c t -> c (ComplexOf t)
    single  :: Container c t => c t -> c (SingleOf t)
    double  :: Container c t => c t -> c (DoubleOf t)
    toComplex   :: (Container c t, RealElement t) => (c t, c t) -> c (Complex t)
    fromComplex :: (Container c t, RealElement t) => c (Complex t) -> (c t, c t)


instance Convert Double where
    real = id
    complex = comp'
    single = single'
    double = id
    toComplex = toComplex'
    fromComplex = fromComplex'

instance Convert Float where
    real = id
    complex = comp'
    single = id
    double = double'
    toComplex = toComplex'
    fromComplex = fromComplex'

instance Convert (Complex Double) where
    real = comp'
    complex = id
    single = single'
    double = id
    toComplex = toComplex'
    fromComplex = fromComplex'

instance Convert (Complex Float) where
    real = comp'
    complex = id
    single = id
    double = double'
    toComplex = toComplex'
    fromComplex = fromComplex'

-------------------------------------------------------------------

type family RealOf x

type instance RealOf Double = Double
type instance RealOf (Complex Double) = Double

type instance RealOf Float = Float
type instance RealOf (Complex Float) = Float

type family ComplexOf x

type instance ComplexOf Double = Complex Double
type instance ComplexOf (Complex Double) = Complex Double

type instance ComplexOf Float = Complex Float
type instance ComplexOf (Complex Float) = Complex Float

type family SingleOf x

type instance SingleOf Double = Float
type instance SingleOf Float  = Float

type instance SingleOf (Complex a) = Complex (SingleOf a)

type family DoubleOf x

type instance DoubleOf Double = Double
type instance DoubleOf Float  = Double

type instance DoubleOf (Complex a) = Complex (DoubleOf a)

type family ElementOf c

type instance ElementOf (Vector a) = a
type instance ElementOf (Matrix a) = a

------------------------------------------------------------

class Build f where
    build' :: BoundsOf f -> f -> ContainerOf f

type family BoundsOf x

type instance BoundsOf (a->a) = Int
type instance BoundsOf (a->a->a) = (Int,Int)

type family ContainerOf x

type instance ContainerOf (a->a) = Vector a
type instance ContainerOf (a->a->a) = Matrix a

instance (Element a, Num a) => Build (a->a) where
    build' = buildV

instance (Element a, Num a) => Build (a->a->a) where
    build' = buildM

buildM (rc,cc) f = fromLists [ [f r c | c <- cs] | r <- rs ]
    where rs = map fromIntegral [0 .. (rc-1)]
          cs = map fromIntegral [0 .. (cc-1)]

buildV n f = fromList [f k | k <- ks]
    where ks = map fromIntegral [0 .. (n-1)]

----------------------------------------------------
-- experimental

class Konst s where
    konst' :: Element e => e -> s -> ContainerOf' s e

type family ContainerOf' x y

type instance ContainerOf' Int a = Vector a
type instance ContainerOf' (Int,Int) a = Matrix a

instance Konst Int where
    konst' = constantD

instance Konst (Int,Int) where
    konst' k (r,c) = reshape c $ konst' k (r*c)

--------------------------------------------------------
-- | conjugate transpose
ctrans :: (Container Vector e, Element e) => Matrix e -> Matrix e
ctrans = liftMatrix conj . trans

-- | Creates a square matrix with a given diagonal.
diag :: (Num a, Element a) => Vector a -> Matrix a
diag v = diagRect 0 v n n where n = dim v

-- | creates the identity matrix of given dimension
ident :: (Num a, Element a) => Int -> Matrix a
ident n = diag (constantD 1 n)

--------------------------------------------------------

findV p x = foldVectorWithIndex g [] x where
    g k z l = if p z then k:l else l

findM p x = map ((`divMod` cols x)) $ findV p (flatten x)

assocV n z xs = ST.runSTVector $ do
        v <- ST.newVector z n
        mapM_ (\(k,x) -> ST.writeVector v k x) xs
        return v

assocM (r,c) z xs = ST.runSTMatrix $ do
        m <- ST.newMatrix z r c
        mapM_ (\((i,j),x) -> ST.writeMatrix m i j x) xs
        return m

accumV v0 f xs = ST.runSTVector $ do
        v <- ST.thawVector v0
        mapM_ (\(k,x) -> ST.modifyVector v k (f x)) xs
        return v

accumM m0 f xs = ST.runSTMatrix $ do
        m <- ST.thawMatrix m0
        mapM_ (\((i,j),x) -> ST.modifyMatrix m i j (f x)) xs
        return m

----------------------------------------------------------------------

condM a b l e t = reshape (cols a'') $ cond a' b' l' e' t'
  where
    args@(a'':_) = conformMs [a,b,l,e,t]
    [a', b', l', e', t'] = map flatten args

condV f a b l e t = f a' b' l' e' t'
  where
    [a', b', l', e', t'] = conformVs [a,b,l,e,t]

