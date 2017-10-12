{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

class PersistEntity record where
    {-@ data EntityField @-}
    data EntityField record :: * -> *

instance PersistEntity Blob where
    {-@ data EntityField record typ where
        BlobXVal :: EntityField Blob {v:Int | v >= 0}
      | BlobYVal :: EntityField Blob Int
    @-}
    data EntityField Blob typ where
        BlobXVal :: EntityField Blob Int
        BlobYVal :: EntityField Blob Int

{-@ data Blob  = B { xVal :: {v:Int | v >= 0}, yVal :: Int } @-}
data Blob  = B { xVal :: Int, yVal :: Int }

{-@ data Update record typ <p :: typ -> Bool> = Update { updateField :: EntityField record typ<p>, updateValue :: typ<p> } @-}
data Update record typ = Update 
    { updateField :: EntityField record typ
    , updateValue :: typ
    } 

{-@ data variance Update covariant covariant contravariant @-}

{-@ createUpdate :: forall a <p :: a -> Bool>. EntityField record a<p> -> a<p> -> Update record a<p> @-}
createUpdate :: EntityField record a -> a -> Update record a
createUpdate field value = Update {
      updateField = field
    , updateValue = value
}

testUpdateQuery :: () -> Update Blob Int
testUpdateQuery () = createUpdate BlobXVal 3

testUpdateQueryFail :: () -> Update Blob Int
testUpdateQueryFail () = createUpdate BlobXVal (-1)
