{-# LANGUAGE EmptyDataDecls, GADTs, ExistentialQuantification #-}

{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--no-totality"                      @-}
{-@ LIQUID "--ple" @-} 


module FieldPolicy (
  EntityField (..),
  get,
  admin
) where

import Prelude hiding (sequence, mapM)

data User = User Integer
  deriving (Show, Eq)

data CreditCard = CreditCard { creditCardNumber :: String, creditCardHolder :: String}

-- Note: this does not successfully attach the abstract refinement
{-@ data EntityField a b <p :: User -> Bool> where
      Field.CreditCardNumber :: EntityField <{\u -> False}> CreditCard String 
    | Field.CreditCardHolder :: EntityField <{\u -> False}> CreditCard String 
@-}
data EntityField a b where
  CreditCardNumber :: EntityField CreditCard String
  CreditCardHolder :: EntityField CreditCard String

data PersistFilter = EQUAL | NEQ

{-@ data Filter a typ <p :: User -> Bool> = Filter { filterFilter :: PersistFilter, filterField :: EntityField <p> a typ, filterValue :: typ } @-}
data Filter a typ =  Filter { filterFilter :: PersistFilter, filterField :: EntityField a typ, filterValue :: typ }
{-@ data variance Filter covariant covariant contravariant @-}

{-@ testFilter :: Filter <{\u -> u == admin}> CreditCard String @-}
testFilter = Filter EQUAL CreditCardHolder ""

