-- https://github.com/ucsd-progsys/liquidhaskell/issues/1473

{-# LANGUAGE GADTs, TypeFamilies, GeneralizedNewtypeDeriving, OverloadedStrings, TemplateHaskell, QuasiQuotes, MultiParamTypeClasses #-}

{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-adt"         @-}
{-  LIQUID "--no-termination" @-}

-- | Description of database records.
module T1473A
  ( User, UserId
  , EntityField(..)
  ) where

data Entity record = Entity (Key record) record

{-@ reflect entityKey @-}
entityKey :: Entity record -> Key record
entityKey (Entity k _) = k

{-@ reflect entityVal @-}
entityVal :: Entity record -> record
entityVal (Entity _ v) = v

{-@ data User = User
     { userName   :: String
     , userFriend :: UserId
     , userSsn    :: Int
     }
@-}

{-@
data EntityField User field <q :: Entity User -> Entity User -> Bool> where
    UserId     :: EntityField <{\row v -> entityKey v = entityKey row}>              User {v:_ | True}
    UserName   :: EntityField <{\row v -> entityKey v = userFriend (entityVal row)}> User {v:_ | True}
    UserFriend :: EntityField <{\row v -> entityKey v = userFriend (entityVal row)}> User {v:_ | True}
    UserSsn    :: EntityField <{\row v -> entityKey v = entityKey row}>              User {v:_ | True}
@-}
{-@ data variance EntityField covariant covariant contravariant @-}

data User = User
  { userName   :: String
  , userFriend :: UserId
  , userSsn    :: Int
  }

class PersistEntity record where
  data Key record
  data EntityField record :: * -> *

type UserId = Key User

instance PersistEntity User where
  data Key User = UserKey Int

  data EntityField User field where
    UserId     :: EntityField User UserId
    UserName   :: EntityField User String
    UserFriend :: EntityField User UserId
    UserSsn    :: EntityField User Int

project1 :: EntityField User field -> Int
project1 UserId   = 0
project1 UserName = 1 
project1 _        = 2 

project :: EntityField User field -> Entity User -> field
project UserId     x = entityKey x
project UserName   x = userName   . entityVal $ x
project UserFriend x = userFriend . entityVal $ x
project UserSsn    x = userSsn    . entityVal $ x
