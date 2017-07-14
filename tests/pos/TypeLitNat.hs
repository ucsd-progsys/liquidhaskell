{-# LANGUAGE GADTs #-}

{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module TypeLits where

import GHC.TypeLits

-- THIS SHOULD BE UNSAFE
miunsafe2 :: MI 0
miunsafe2 = Small 0

data MI (s :: Nat)
  = Small { mi_input :: Int  }

{-@ Small :: forall (s :: Nat). {v:Int | s ~~ v } -> MI s @-}

-- data Vector a n where
--  VNil  :: Vector a 0
--  VCons :: a -> Vector a n -> Vector a (1 + n)

-- fromList        :: [a] -> forall (n :: Nat). Vector a n
-- fromList []     = VNil
-- fromList (x:xs) = VCons x (fromList xs)


-- OR

{- data MI (s :: Symbol)
    = Small { mi_input :: {v:String | v == s } } @-}
