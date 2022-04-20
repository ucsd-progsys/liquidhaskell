{-@ LIQUID "--exact-data-con" @-}

{-# LANGUAGE  GADTs #-}

module ExactGADT2 where

{-@ data Field typ where
        FldX :: Field Int
        FldY :: Field Int
  @-}

data Field typ where
  FldX :: Field Int
  FldY :: Field Int

poogle = FldY
