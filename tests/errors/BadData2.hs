{-@ LIQUID "--exact-data-cons" @-}

module Boo where

{-@ data Hog where  
      Cuthb :: Nat -> T 
  @-}

data Hog = H Int 

data T = Cuthb { fldX :: Int }

zoink = Cuthb (-1)
