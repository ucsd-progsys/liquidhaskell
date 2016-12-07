{-# LANGUAGE DataKinds #-}

module ProxyClass where

import           Data.Proxy


{-@ sizeOfMember :: Proxy a -> Nat @-}
sizeOfMember :: Proxy a -> Int
sizeOfMember = undefined 