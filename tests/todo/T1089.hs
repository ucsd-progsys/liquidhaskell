
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

module Query where

import Prelude hiding (filter)

data PersistFilter = EQUAL | LE | GE

-- class PersistEntity record where
    {- data EntityField @-}
    -- data EntityField record :: * -> *

{- data Filter record typ = Filter { filterField :: EntityField record typ, filterValue :: typ, filterFilter :: PersistFilter } @-}
data Filter typ = Filter
  { filterField  :: EntityField typ
  , filterValue  :: typ
  , filterFilter :: PersistFilter
  }

createEqQuery :: EntityField typ -> typ -> Filter typ
createEqQuery field value = Filter
  { filterField  = field
  , filterValue  = value
  , filterFilter = EQUAL
  }

data Blob  = B { xVal :: Int, yVal :: Int }

--instance PersistEntity Blob where
    {- data EntityField record typ where
        BlobXVal :: EntityField Blob Int
      | BlobYVal :: EntityField Blob Int
    @-}
data EntityField typ where
   BlobXVal :: EntityField Int
   BlobYVal :: EntityField Int

{-@ filter :: f:(a -> Bool) -> [a] -> [{v:a | f v}] @-}
filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x         = x : filter f xs
  | otherwise   =     filter f xs
filter _ []     = []


{-@ reflect evalQBlobXVal @-}
evalQBlobXVal :: Int -> Int -> Bool
evalQBlobXVal filter given = filter == given

{-@ reflect evalQBlobYVal @-}
evalQBlobYVal :: Int -> Int -> Bool
evalQBlobYVal filter given = filter == given

{-@ reflect evalQBlob @-}
evalQBlob :: Filter typ -> Blob -> Bool
evalQBlob filter blob = case filterField filter of
    BlobXVal -> evalQBlobXVal (filterValue filter) (xVal blob)
    BlobYVal -> evalQBlobYVal (filterValue filter) (yVal blob)

{-@ filterQBlob :: f:(Filter a) -> [Blob] -> [{b:Blob | evalQBlob f b}] @-}
filterQBlob :: Filter a -> [Blob] -> [Blob]
filterQBlob q = filter (evalQBlob q)
