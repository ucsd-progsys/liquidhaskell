{-# LANGUAGE GADTs, TypeFamilies #-}
module T1477 where

class PersistEntity record where
    data EntityField record :: * -> *

data User = User

instance PersistEntity User where
  {-@ data EntityField User field  where
          UserId     :: EntityField User _
          UserName   :: EntityField User _ 
          UserFriend :: EntityField User _ 
          UserSsn    :: EntityField User _ 
    @-}
  data EntityField User typ
    = typ ~ Int => UserId      |
      typ ~ String => UserName |
      typ ~ Int => UserFriend  |
      typ ~ Int => UserSsn

