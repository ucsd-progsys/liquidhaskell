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
  {-@ data EntityField Blob typ where
            BlobXVal :: EntityField Blob {v:_ | True }
          | BlobYVal :: EntityField Blob {v:_ | True }
    @-}
  -- ORIG
  -- data EntityField Blob typ where
     -- BlobXVal :: EntityField Blob Int
     -- BlobYVal :: EntityField Blob Int

  -- TH-GEN
  data EntityField Blob typ
    = typ ~ Int => BlobXVal |
      typ ~ Int => BlobYVal

data RefinedFilter record typ = RefinedFilter
  { refinedFilterField  :: EntityField record typ
  -- , refinedFilterValue  :: typ
  -- , refinedFilterFilter :: RefinedPersistFilter
  }

{- reflect evalQBlob @-}
evalQBlob :: RefinedFilter Blob typ -> Blob -> Bool
evalQBlob filter blob = case refinedFilterField filter of
  BlobXVal -> True
  BlobYVal -> True

{-@ reflect foo @-}
foo :: RefinedFilter Blob typ -> Blob -> Bool
foo (RefinedFilter BlobXVal) blob = True
foo (RefinedFilter BlobYVal) blob = True
