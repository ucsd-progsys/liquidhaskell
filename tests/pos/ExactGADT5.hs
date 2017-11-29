{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--ple" @-} 

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

module Query where

import Prelude hiding (filter)

data PersistFilter = EQUAL | LE | GE

class PersistEntity record where
    {-@ data EntityField @-}
    data EntityField record :: * -> *

{-@ data Filter record typ = Filter { filterField :: EntityField record typ, filterValue :: typ, filterFilter :: PersistFilter } @-}
data Filter record typ = Filter
    { filterField  :: EntityField record typ
    , filterValue  :: typ
    , filterFilter :: PersistFilter
    } 

{-@ reflect createEqQuery @-}
createEqQuery :: (PersistEntity record, Eq typ) => 
                 EntityField record typ -> typ -> Filter record typ
createEqQuery field value = Filter field value EQUAL
{- 
  Filter {
    filterField = field
  , filterValue = value
  , filterFilter = EQUAL
  }
-}

createLeQuery :: (PersistEntity record, Eq typ) => 
                 EntityField record typ -> typ -> Filter record typ
createLeQuery field value =
  Filter {
    filterField = field
  , filterValue = value
  , filterFilter = LE 
  }

{-@ data Blob  = B { xVal :: Int, yVal :: Int } @-}
data Blob  = B { xVal :: Int, yVal :: Int }

instance PersistEntity Blob where
    {-@ data EntityField record typ where
        BlobXVal :: EntityField Blob Int
      | BlobYVal :: EntityField Blob Int
    @-}
    data EntityField Blob typ where
        BlobXVal :: EntityField Blob Int
        BlobYVal :: EntityField Blob Int

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
evalQBlobXVal GE filter given = given >= filter

{-@ reflect evalQBlobYVal @-}
evalQBlobYVal :: PersistFilter -> Int -> Int -> Bool
evalQBlobYVal EQUAL filter given = filter == given
evalQBlobYVal LE filter given = given <= filter
evalQBlobYVal GE filter given = given >= filter

{-@ reflect evalQBlob @-}
evalQBlob :: Filter Blob typ -> Blob -> Bool
evalQBlob filter blob = case filterField filter of
    BlobXVal -> evalQBlobXVal (filterFilter filter) (filterValue filter) (xVal blob)
    BlobYVal -> evalQBlobYVal (filterFilter filter) (filterValue filter) (yVal blob)

{-@ filterQBlob :: f:(Filter Blob a) -> [Blob] -> [{b:Blob | evalQBlob f b}] @-}
filterQBlob :: Filter Blob a -> [Blob] -> [Blob]
filterQBlob q = filter (evalQBlob q)

{-@ assume select :: f:(Filter Blob a) -> [{b:Blob | evalQBlob f b}] @-}
select :: Filter Blob a -> [Blob]
select _ = undefined

-- Client code:

-- Should typecheck:
{-@ getZeros :: [Blob] -> [{b:Blob | xVal b == 0}] @-}
getZeros :: [Blob] -> [Blob]
-- getZeros = filterQBlob  (Filter BlobXVal 0 EQUAL) -- (createEqQuery BlobXVal 0) blobs 
getZeros = filterQBlob (createEqQuery BlobXVal 0) 

{-@ getZeros_ :: () -> [{b:Blob | xVal b == 0}] @-}
getZeros_ :: () -> [Blob]
-- getZeros_ () = select (Filter BlobXVal 0 EQUAL) -- (createEqQuery BlobXVal 0)
getZeros_ () = select (createEqQuery BlobXVal 0)
