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

