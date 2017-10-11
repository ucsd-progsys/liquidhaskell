{-@ LIQUID "--exact-data-con"                      @-}

{-# LANGUAGE  GADTs #-}

module Query where

data Field typ where
  FldX :: Field Int
  FldY :: Field Int

poogle = FldY
