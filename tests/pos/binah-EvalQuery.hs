{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--ple" @-} 

{-@ infixr === @-}
{-@ infixr >== @-}
{-@ infixr <== @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

module Query where

import Prelude hiding (filter)

data PersistFilter = EQUAL | LE | GE

class PersistEntity record where
    data EntityField record :: * -> *

{-@ data Filter record typ = Filter { filterField :: EntityField record typ, filterValue :: typ, filterFilter :: PersistFilter } @-}
data Filter record typ = Filter
    { filterField  :: EntityField record typ
    , filterValue  :: typ
    , filterFilter :: PersistFilter
    } 


{-@ reflect === @-}
(===) :: (PersistEntity record, Eq typ) => 
                 EntityField record typ -> typ -> Filter record typ
field === value = Filter field value EQUAL

{-@ reflect <== @-}
(<==) :: (PersistEntity record, Eq typ) => 
                 EntityField record typ -> typ -> Filter record typ
field <== value =
  Filter {
    filterField = field
  , filterValue = value
  , filterFilter = LE 
  }

{-@ reflect >== @-}
(>==) :: (PersistEntity record, Eq typ) => 
                 EntityField record typ -> typ -> Filter record typ
field >== value =
  Filter {
    filterField = field
  , filterValue = value
  , filterFilter = GE 
  }

{-@ data Blob  = B { xVal :: Int, yVal :: Int } @-}
data Blob  = B { xVal :: Int, yVal :: Int }

instance PersistEntity Blob where
    {-@ data EntityField Blob typ where
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

{-@ reflect evalQsBlob @-}
evalQsBlob :: [Filter Blob typ] -> Blob -> Bool
evalQsBlob (f:fs) blob = evalQBlob f blob && (evalQsBlob fs blob)
evalQsBlob [] _ = True


{-@ filterQBlob :: f:(Filter Blob a) -> [Blob] -> [{b:Blob | evalQBlob f b}] @-}
filterQBlob :: Filter Blob a -> [Blob] -> [Blob]
filterQBlob q = filter (evalQBlob q)

{-@ filterQsBlob :: f:[(Filter Blob a)] -> [Blob] -> [{b:Blob | evalQsBlob f b}] @-}
filterQsBlob :: [Filter Blob a] -> [Blob] -> [Blob]
filterQsBlob qs = filter (evalQsBlob qs)

-- select functions

{-@ assume selectBlob :: f:[(Filter Blob a)] -> [{b:Blob | evalQsBlob f b}] @-}
selectBlob :: [Filter Blob a] -> [Blob]
selectBlob fs = undefined 

{-@ getZeros_ :: () -> [{b:Blob | xVal b = 0}] @-}
getZeros_ :: () -> [Blob]
getZeros_ () = selectBlob [(Filter BlobXVal 0 EQUAL)]

{-@ getBiggerThan10 :: () -> [{b:Blob | xVal b >= 10}] @-}
getBiggerThan10 :: () -> [Blob]
getBiggerThan10 () = selectBlob [(Filter BlobXVal 11 GE)]

{-@ getInRange :: () -> [{b:Blob | xVal b >= 10  && xVal b <= 20 && yVal b >= 0 && yVal b <= 11}] @-}
getInRange :: () -> [Blob]
getInRange () = selectBlob [ (BlobXVal >== 10)
                           , (BlobXVal <== 20)
                           , (BlobYVal >== 0)
                           , (BlobYVal <== 11)
                           ]
