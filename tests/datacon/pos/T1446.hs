{-# LANGUAGE GADTs, TypeFamilies, GeneralizedNewtypeDeriving, OverloadedStrings, TemplateHaskell, QuasiQuotes, MultiParamTypeClasses #-}

{-@ LIQUID "--no-adt"     @-}
{-@ LIQUID "--reflection" @-}

module T1446 where

data BlobId = BlobId 

data Blob = Blob 
  { blobName   :: String
  , blobFriend :: BlobId
  , blobSsn    :: Int
  }

instance PersistEntity Blob where
  {-@ data EntityField Blob typ <q :: Entity Blob -> Entity Blob -> Bool> where
          T1446.BlobName   :: EntityField <{\row v -> entityKey v = bblobFriend (entityVal row)}> Blob {v:_ | True}
          T1446.BlobFriend :: EntityField <{\row v -> entityKey v = bblobFriend (entityVal row)}> Blob {v:_ | True}
          T1446.BlobSsn    :: EntityField <{\row v -> entityKey v = entityKey             row }> Blob {v:_ | True}
    @-}
   data EntityField Blob typ where 
     BlobName   :: EntityField Blob String 
     BlobFriend :: EntityField Blob BlobId 
     BlobSsn    :: EntityField Blob Int 

{-@ data variance EntityField covariant covariant contravariant @-}
class PersistEntity record where
  data EntityField record :: * -> *

data Entity r = Entity BlobId r  

{-@ measure bblobFriend @-}
bblobFriend :: Blob -> BlobId 
bblobFriend (Blob _ k _) = k 

{-@ measure entityKey @-}
entityKey :: Entity r -> BlobId 
entityKey (Entity k _) = k 

{-@ measure entityVal @-}
entityVal :: Entity r -> r
entityVal (Entity _ k) = k 

project :: EntityField Blob a -> Blob -> a
project BlobName   = blobName
project BlobFriend = blobFriend
project BlobSsn    = blobSsn
