{-# LANGUAGE EmptyDataDecls, GADTs, ExistentialQuantification #-}

{-@ LIQUID "--no-adt" 	      @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--higherorder"    @-}

module Field where

data CreditCard = CreditCard { creditCardNumber :: Int, creditCardHolder :: [Char]}

data EntityField a b where
  CreditCardNumber :: EntityField CreditCard Int
  CreditCardHolder :: EntityField CreditCard [Char]

------------------------------------------------------------------------------------------
data RefinedPersistFilter = EQUAL

data RefinedFilter record typ = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    } 

{-@ reflect foo @-}
foo :: RefinedPersistFilter -> Int -> RefinedFilter CreditCard Int
foo f v = RefinedFilter CreditCardNumber v f

------------------------------------------------------------------------------------------

