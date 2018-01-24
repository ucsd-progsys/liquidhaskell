{-@ LIQUID "--exact-data-con" @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

module Query where
-----------------------------------

{- data Goob a where
       GooX :: (a ~ Int) => Goob a
    |  GooY :: (a ~ Int) => Goob a
  @-}


-- data Goob a where
  -- GooX :: (a ~ Int) => Goob a
  -- GooY :: (a ~ Int) => Goob a

class PersistEntity record where
    data EntityField record :: * -> *

{-@ data Blob  = B { xVal :: Int, yVal :: Int } @-}
data Blob  = B { xVal :: Int, yVal :: Int }

instance PersistEntity Blob where
  {- data EntityField Blob typ where
            BlobXVal :: EntityField Blob Int
          | BlobYVal :: EntityField Blob Int
    @-}
  -- ORIG
  -- data EntityField Blob typ where
     -- BlobXVal :: EntityField Blob Int
     -- BlobYVal :: EntityField Blob Int

  -- TH-GEN
  data EntityField Blob typ
    = typ ~ Int => BlobXVal |
      typ ~ Int => BlobYVal
