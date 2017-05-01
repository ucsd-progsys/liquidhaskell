{-# Language EmptyDataDecls #-}
module Privileges where

import RIO
import Data.Map
import Data.Set

{-@ embed Map as Map_t @-}
{-@ measure Map_select :: Map k v -> k -> v @-}
{-@ measure Map_store  :: Map k v -> k -> v -> Map k v @-}

data Privilege

{-@ measure pread :: Privilege -> Bool @-}
{-@ measure pwrite :: Privilege -> Bool @-}
{-@ measure plookup :: Privilege -> Bool @-}
{-@ measure pcontents :: Privilege -> Bool @-}
{-@ measure pcreateFile :: Privilege -> Bool @-}
{-@ measure pcreateDir :: Privilege -> Bool @-}
{-@ measure pcreateFilePrivs :: Privilege -> Privilege @-}
