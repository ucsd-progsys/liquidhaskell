{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | Implements key mechanisms of Awake.Data.Struct without
-- any additional bounds checking beyond what is documented.
module ClassKind where

import           Data.Proxy
class Member a where

  {-@ class Member a where
       sizeOfMember :: Proxy a -> Nat 
    @-}

  sizeOfMember :: Proxy a -> Int

