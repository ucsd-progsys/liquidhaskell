{-# LANGUAGE GADTs, TypeFamilies #-}
{-@ LIQUID "--exact-data-cons" @-}
-- * Models
class PersistEntity record where
  data EntityField record :: * -> *

-- ** User
{-@
data User = User
  { userId :: Int
  }
@-}
data User = User
  { userId :: Int
--   , userName :: String
--   , userFriend :: Int
--   , userSSN :: String
  } 

instance PersistEntity User where
  data EntityField User typ where
    UserId :: EntityField User Int
--     UserName :: EntityField User String
--     UserFriend :: EntityField User Int
--     UserSSN :: EntityField User String

{-@ inline policy @-}
policy :: EntityField User typ -> User -> User -> Bool
policy UserId row viewer = True
--  policy UserName row viewer = userId viewer == userFriend row
-- policy UserFriend row viewer = userId viewer == userFriend row
-- policy UserSSN row viewer = userId viewer == userId row