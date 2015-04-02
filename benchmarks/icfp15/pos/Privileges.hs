{-# Language EmptyDataDecls #-}
module Privileges where

import RIO
import Data.Map
import Data.Set

{-@ embed Map as Map_t @-}
{-@ measure Map_select :: Map k v -> k -> v @-}
{-@ measure Map_store  :: Map k v -> k -> v -> Map k v @-}

data Privilege

{-@ measure pread :: Privilege -> Prop @-}
{-@ measure pwrite :: Privilege -> Prop @-}
{-@ measure plookup :: Privilege -> Prop @-}
{-@ measure pcontents :: Privilege -> Prop @-}
{-@ measure pcreateFile :: Privilege -> Prop @-}
{-@ measure pcreateDir :: Privilege -> Prop @-}
{-@ measure pcreateFilePrivs :: Privilege -> Privilege @-}

main = ()