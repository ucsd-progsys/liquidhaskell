{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-con" @-}


module ExactGADT0 where

data Value a where
  VInt  :: Int  -> Value Int
  VBool :: Bool -> Value Bool
