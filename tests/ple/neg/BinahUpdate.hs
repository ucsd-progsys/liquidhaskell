{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--ple" @-} 

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

module BinahUpdate where

class PersistEntity record where
    data EntityField record typ :: *

instance PersistEntity Blob where
    {-@ data EntityField Blob typ where
            BlobXVal :: EntityField Blob {v:Int | v >= 66}
            BlobYVal :: EntityField Blob Int
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
