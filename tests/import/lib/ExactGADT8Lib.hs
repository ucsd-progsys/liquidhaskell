{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt"     @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

--------------------------------------------------------------------------------
module ExactGADT8Lib where

class PersistEntity record where
    data EntityField record :: * -> *

{-@ data Blob  = Bingo { xVal :: Int, yVal :: Int } @-}
data Blob  = Bingo { xVal :: Int, yVal :: Int }

instance PersistEntity Blob where
  data EntityField Blob typ where
    BlobXVal :: EntityField Blob Int
    BlobYVal :: EntityField Blob Int

data RefinedFilter record typ = RefinedFilter
  { refinedFilterField  :: EntityField record typ
  }

evalQBlob :: RefinedFilter Blob typ -> Blob -> Bool
evalQBlob filter blob = case refinedFilterField filter of
  BlobXVal -> True
  BlobYVal -> True

{-@ reflect foo @-}
foo :: RefinedFilter Blob typ -> Blob -> Bool
foo (RefinedFilter BlobXVal) blob = True
foo (RefinedFilter BlobYVal) blob = True
