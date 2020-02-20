{-@ LIQUID "--typed-holes" @-}

module User where

{-@ err :: { v: Int | false } -> a @-}
err :: Int -> a
err s = undefined

{-@ measure length' @-}
{-@ length' :: [a] -> Nat @-}
length' :: [a] -> Int
length' []     = 0
length' (x:xs) = 1 + length' xs
  
{-@ append :: xs: [a] -> ys: [a] -> { v: [a] | length' v == length' xs + length' ys } 
  @-}
append :: [a] -> [a] -> [a]
append []     ys = ys
append (x:xs) ys = x : append xs ys
  
data Info = Info { sa :: Int, zc :: Int, loc :: Bool } 
    
data Address = Address { i :: Info, priv :: Bool }
  
{-@ measure isPriv @-}
{-@ isPriv :: Address -> Bool @-}
isPriv (Address _ priv) = priv  
  
{-@ getPriv :: a:Address -> { v: Bool | v == isPriv a } @-}
getPriv :: Address -> Bool
getPriv a = isPriv a

{-@ data AddressBook = AddressBook { x :: [{v: Address | isPriv v}], y :: [{v: Address | not (isPriv v)}] }
  @-}
data AddressBook = AddressBook [Address] [Address] 

{-@ measure size @-}
{-@ size :: AddressBook -> Nat @-}
size :: AddressBook -> Int
size (AddressBook bs ps) = length' bs + length' ps
  
{-@ mergeAddressBooks :: a: AddressBook -> b: AddressBook -> {v: AddressBook | size v == size a + size b} @-}
mergeAddressBooks :: AddressBook -> AddressBook -> AddressBook
mergeAddressBooks = _goal
-- mergeAddressBooks a b =
--     case a of
--       AddressBook x2 x3 -> 
--         case b of
--           AddressBook x6 x7 -> AddressBook (append x2 x6) (append x3 x7)
