{-@ LIQUID "--exact-data-con" @-}

{-# LANGUAGE  GADTs #-}

module Query where

data Field typ where
  FldX :: Int -> Field Int
  FldY :: Int -> Field Int

{-@ reflect foo @-}
foo :: Field a -> Int 
foo (FldX x) = x
foo (FldY y) = y
