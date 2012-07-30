{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Wrap0 where


import Language.Haskell.Liquid.Prelude (liquidError, liquidAssertB)
import Data.Function (on)
import Data.Ord (comparing)

{-@ data WrapTypeGen b a <p :: b -> Bool> = WrapType (f :: b <p>) (gv :: a) @-}
data WrapTypeGen b a = WrapType {getVect :: b, getVal :: a}

type WrapType a      = WrapTypeGen [Double] a

instance Eq (WrapType a) where
   (==) = (==) `on` getVect

instance Ord (WrapType a) where
    compare = comparing getVect

{-@ assert flibXs :: a -> Bool @-}
flibXs x              = prop1 (WrapType [x, x, x] x)
prop1 (WrapType [] _) = liquidError "no!"
prop1 (WrapType _  _) = True

{-@ assert nflibXs :: Int -> a -> Bool @-}
nflibXs n x           = prop2 n (WrapType nxs x)
                        where nxs = replicate n x 

prop2 n (WrapType xs _) = liquidAssertB (n == length xs) 





