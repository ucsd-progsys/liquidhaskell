{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--exact-data-con" @-}


module Zong where

data Value a where
  VInt  :: Int  -> Value Int
  VBool :: Bool -> Value Bool
