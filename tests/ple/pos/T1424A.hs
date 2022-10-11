
{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module T1424A where


-- Placeholder for Data.Persistent's Filter type
data Filter a = Filter

{-@ data RefinedFilter record <r :: record -> Bool, q :: record -> User -> Bool> = RefinedFilter (Filter record) @-}
data RefinedFilter record = RefinedFilter (Filter record)

{-@
data User = User
     { userId   :: Int,
       userName :: String
     , userFriend :: Int
     , userSSN    :: Int
     }
@-}
data User = User { userId::Int, userName :: String, userFriend :: Int, userSSN :: Int }
    deriving (Eq, Show)

{-@
data EntityField record typ where
   UserName :: EntityField User String
   UserFriend :: EntityField User Int
   UserSSN :: EntityField  User Int
@-}
data EntityField a b where
  UserName :: EntityField User String
  UserFriend :: EntityField User Int
  UserSSN :: EntityField User Int

{-@ reflect policy @-}
policy :: EntityField a b -> a -> User -> Bool
policy UserName row v = userId v == userFriend row
policy UserFriend row v = userId v == userFriend row
policy UserSSN row v = userId v == userId row

{-@ reflect project @-}
project :: EntityField a b -> a -> b
project UserName user = userName user
project UserFriend user = userFriend user
project UserSSN user = userSSN user

{-@
(==.) :: field:EntityField a b -> val:b -> RefinedFilter<{\row -> project field row == val}, {\row v -> policy field row v}> a
@-}
(==.) :: EntityField a b -> b -> RefinedFilter a
field ==. val = RefinedFilter Filter
