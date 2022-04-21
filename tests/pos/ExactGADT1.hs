{-@ LIQUID "--exact-data-con" @-}

{-# LANGUAGE  GADTs #-}

module ExactGADT1 where

data Field typ where
  FldX :: Field Int
  FldY :: Field Int

poogle = FldY
