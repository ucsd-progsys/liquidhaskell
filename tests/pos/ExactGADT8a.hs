{-@ LIQUID "--exact-data-con" @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

module ExactGADT8a where

{- data EntityField typ where
            BlobXVal :: EntityField {v:_ | True }
          | BlobYVal :: EntityField {v:_ | True }
 @-}
data EntityField typ where
  BlobXVal :: EntityField Int
  BlobYVal :: EntityField Int

  -- TH-GEN
  -- data EntityField Blob typ
  --  = typ ~ Int => BlobXVal |
  --    typ ~ Int => BlobYVal

{-@ reflect evalQBlob @-}
evalQBlob :: EntityField a -> Bool 
evalQBlob BlobXVal = True 
evalQBlob BlobYVal = False 

