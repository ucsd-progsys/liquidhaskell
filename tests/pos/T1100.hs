{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--no-adt"                              @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

class PersistEntity record where
    data EntityField record :: * -> *

instance PersistEntity Blob where
  {-@ data EntityField Blob typ where
        BlobXVal :: EntityField Blob {v:Int | v >= 0}
      | BlobYVal :: EntityField Blob Int
    @-}
    data EntityField Blob typ where
        BlobXVal :: EntityField Blob Int
        BlobYVal :: EntityField Blob Int

{-@ data Blob  = B { xVal :: {v:Int | v >= 0}, yVal :: Int } @-}
data Blob  = B { xVal :: Int, yVal :: Int }

{-@ data UpdateT record typ = Update { updateField :: EntityField record typ, updateValue :: typ } @-}
data UpdateT record typ = Update
    { updateField :: EntityField record typ
    , updateValue :: typ
    }

{-@ createUpdate :: forall a <p :: a -> Bool>. EntityField record a<p> -> a<p> -> UpdateT record a<p> @-}
createUpdate :: EntityField record a -> a -> UpdateT record a
createUpdate field value = Update {
      updateField = field
    , updateValue = value
}

testUpdateQuery :: () -> UpdateT Blob Int
testUpdateQuery () = createUpdate BlobXVal 3
