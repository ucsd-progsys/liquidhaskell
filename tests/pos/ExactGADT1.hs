{-@ LIQUID "--exact-data-con"                      @-}

{-# LANGUAGE  GADTs #-}

module Query where

data Field typ where
  FldX :: Field Int
  FldY :: Field Int

poogle = FldY

data Goob a where
  GooX :: (a ~ Int) => Goob a
  GooY :: (a ~ Int) => Goob a



