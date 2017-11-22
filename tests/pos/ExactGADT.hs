{-# LANGUAGE  GADTs #-}

module Query where

{-@ data Field typ where
        FldX :: Field Int
      | FldY :: Field Int
  @-}

data Field typ where
  FldX :: Field Int
  FldY :: Field Int

bob = FldX 
