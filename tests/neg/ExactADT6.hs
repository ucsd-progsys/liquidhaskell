{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--exact-data-con" @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

{-@ data EntityField typ where
        BlobXVal :: EntityField {v:Int | v >= 0}
      | BlobYVal :: EntityField Int
  @-}

data EntityField typ where
  BlobXVal :: EntityField Int
  BlobYVal :: EntityField Int

{-@ blobXVal :: EntityField {v:Int | v >= 0} @-}
blobXVal :: EntityField Int
blobXVal = BlobXVal

{- data Update record typ = Update { updateField :: EntityField record typ, updateValue :: typ } @-}
data Update typ = Update 
    { updateField :: EntityField typ
    , updateValue :: typ
    } 

{-@ createUpdate :: EntityField a -> a -> Update a @-}
createUpdate :: EntityField a -> a -> Update a
createUpdate field value = Update 
  { updateField = field
  , updateValue = value
  }


-- BAD
testUpdateQueryFail :: () -> Update Int
testUpdateQueryFail () = createUpdate BlobXVal (-1)

