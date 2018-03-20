{-# LANGUAGE EmptyDataDecls, GADTs, ExistentialQuantification #-}

{-@ LIQUID "--no-adt" 	       @-}
{-@ LIQUID "--exact-data-con"  @-}
{-@ LIQUID "--no-totality"     @-}

module FieldPolicy where

data User = User Integer
  deriving (Show, Eq)

{-@ reflect admin @-}
admin = User 0

data CreditCard = CreditCard 
  { creditCardNumber :: String
  , creditCardHolder :: String
  }

-- Note: this does not successfully attach the abstract refinement
{-@ data EntityField <p :: User -> Bool> where
      FieldPolicy.CreditCardNumber :: EntityField <{\u -> False}> 
    | FieldPolicy.CreditCardHolder :: EntityField <{\u -> False}> 
  @-}
data EntityField where
  CreditCardNumber :: EntityField 
  CreditCardHolder :: EntityField

data PersistFilter = EQUAL | NEQ

{-@ data Filter a typ <p :: User -> Bool> = Filter { filterFilter :: PersistFilter, filterField :: EntityField <p>, filterValue :: typ } @-}
data Filter a typ =  Filter { filterFilter :: PersistFilter, filterField :: EntityField, filterValue :: typ }
{-@ data variance Filter covariant covariant contravariant @-}

{-@ testFilter :: Filter <{\u -> u == admin}> CreditCard String @-}
testFilter :: Filter CreditCard String
testFilter = Filter EQUAL CreditCardHolder ""

