-- TODO-REBARE-EQ-REPR: GHC shifts the representation of the ~ to something new with 8.4.3 maybe?

-- https://github.com/ucsd-progsys/liquidhaskell/issues/1295

{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}

{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--no-termination" @-}


--------------------------------------------------------------------------------
module TypeEquality01 where

class PersistEntity record where
    data EntityField record :: * -> *
    fooMeth :: EntityField record a -> Int

data Person = Person 
  { personNumber :: Int
  , personName :: String
  , personNums :: [Int]
  } 

instance PersistEntity Person where
  {-@ data EntityField Person typ where
          TypeEquality01.PersonNumber :: EntityField Person {v:_ | 0 <= v   }
          TypeEquality01.PersonName   :: EntityField Person {v:_ | 0 < len v}
          TypeEquality01.PersonNums   :: EntityField Person {v:_ | 0 < len v}
    @-}
  data EntityField Person typ
    = typ ~ Int => PersonNumber |
      typ ~ String => PersonName |
      typ ~ [Int] => PersonNums

  fooMeth PersonNums = 10 
  fooMeth _          = 0

