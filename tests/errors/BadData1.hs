{-@ LIQUID "--expect-error-containing=Data constructors in refinement do not match original datatype for `EntityField`" @-}
{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--exact-data-con" @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

module BadData1 where

class PersistEntity record where
    data EntityField record :: * -> *

-- The reason this fails is because the refinement uses 'record'
-- instead of 'Blob'. Therefore, the lookup for the GHC datatype
-- will return no constructors, and consequently, LH complains
-- that our refinement has two.
--
instance PersistEntity Blob where
    {-@ data EntityField record typ where
           BlobXVal :: EntityField Blob {v:Int | v >= 0}
           BlobYVal :: EntityField Blob Int
    @-}
    data EntityField Blob typ where
        BlobXVal :: EntityField Blob Int
        BlobYVal :: EntityField Blob Int


{-@ data Blob  = B { xVal :: {v:Int | v >= 0}, yVal :: Int } @-}
data Blob = B { xVal :: Int, yVal :: Int }

{-@ blobXVal :: EntityField Blob {v:Int | v >= 0} @-}
blobXVal :: EntityField Blob Int
blobXVal = BlobXVal

-- OK
-- testUpdateQuery :: () -> Update Blob Int
-- testUpdateQuery () = createUpdate blobXVal 3

-- BAD
-- testUpdateQueryFail :: () -> Update Blob Int
-- testUpdateQueryFail () = createUpdate blobXVal (-1)

main :: IO ()
main = pure ()
