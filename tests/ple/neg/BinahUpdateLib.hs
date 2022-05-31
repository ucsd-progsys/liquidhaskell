{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--ple" @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

module BinahUpdateLib where

class PersistEntity record where
    data EntityField record typ :: *

instance PersistEntity Blob where
    {-@ data EntityField Blob typ where
            BinahUpdateLib.BlobYVal :: EntityField Blob {v:_ | True}
            BinahUpdateLib.BlobXVal :: EntityField Blob {v:_ | v >= 10}
      @-}
    data EntityField Blob typ where
        BlobXVal :: EntityField Blob Int
        BlobYVal :: EntityField Blob Int

{-@ data Blob  = B { xVal :: {v:Int | v >= 0}, yVal :: Int } @-}
data Blob  = B { xVal :: Int, yVal :: Int }

data Update record typ = Update
    { updateField :: EntityField record typ
    , updateValue :: typ
    }

createUpdate :: EntityField record a -> a -> Update record a
createUpdate field value = Update {
      updateField = field
    , updateValue = value
}

testUpdateQuery :: () -> Update Blob Int
testUpdateQuery () = createUpdate BlobXVal 8  -- toggle to 80 to be SAFE
