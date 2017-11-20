{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{- LIQUID "--automatic-instances=liquidinstances" @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

module Query where

import Prelude hiding (filter)

data PersistFilter = EQUAL | LE | GE

class PersistEntity record where
  data EntityField record :: * -> *

{-@ 
data Filter record typ = Filter
    { filterField  :: EntityField record typ
    , filterValue  :: typ
    , filterFilter :: PersistFilter
    }
@-}


data Filter record typ = Filter
    { filterField  :: EntityField record typ
    , filterValue  :: typ
    , filterFilter :: PersistFilter
    }

createEqQuery :: (PersistEntity record, Eq typ) =>
                 EntityField record typ -> typ -> Filter record typ
createEqQuery field value =
  Filter {
    filterField = field
  , filterValue = value
  , filterFilter = EQUAL
  }

{-@ data Blob = B { xVal :: Int, yVal :: Int } @-}
data Blob = B { xVal :: Int, yVal :: Int }

instance PersistEntity Blob where
  data EntityField Blob dog where
    BlobXVal :: EntityField Blob Int
    BlobYVal :: EntityField Blob Int

floog = BlobXVal 

{-@ filter :: f:(a -> Bool) -> [a] -> [{v:a | f v}] @-}
filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x         = x : filter f xs
  | otherwise   =     filter f xs
filter _ []     = []

{-@ reflect evalQBlobXVal @-}
evalQBlobXVal :: PersistFilter -> Int -> Int -> Bool
evalQBlobXVal EQUAL filter given = filter == given
evalQBlobXVal LE filter given = given <= filter
evalQBlobXVal GE filter given = given <= filter

{-@ reflect evalQBlobYVal @-}
evalQBlobYVal :: PersistFilter -> Int -> Int -> Bool
evalQBlobYVal EQUAL filter given = filter == given
evalQBlobYVal LE filter given = given <= filter
evalQBlobYVal GE filter given = given <= filter

{-@ reflect evalQBlob @-}
evalQBlob :: Filter Blob typ -> Blob -> Bool
evalQBlob filter blob = case filterField filter of
  BlobXVal -> {- goo (filterValue filter) -} evalQBlobXVal (filterFilter filter) (filterValue filter) (xVal blob)
  BlobYVal -> {- goo (filterValue filter) -} evalQBlobYVal (filterFilter filter) (filterValue filter) (yVal blob)

{-@ reflect goo @-}
goo :: Int -> Bool 
goo n = if n == 0 then True else False 

{-@ filterQBlob :: f:(Filter Blob a) -> [Blob] -> [{b:Blob | evalQBlob f b}] @-}
filterQBlob :: Filter Blob a -> [Blob] -> [Blob]
filterQBlob q = filter (evalQBlob q)
