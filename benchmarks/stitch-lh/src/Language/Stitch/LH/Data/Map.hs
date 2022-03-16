{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-# OPTIONS_GHC -fenable-rewrite-rules -Wno-inline-rule-shadowing #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.Data.Map
-- Copyright   :  (C) 2021 Facundo Domínguez
-- License     :  BSD-style (see LICENSE)
-- Stability   :  experimental
--
-- An interface of maps that can be used in reflected definitions
-- with LH. It is not currently used in the rest of stitch-lh, but
-- I'm keeping it for now, just for the record.
--
-- The ability to reflect operations on Maps comes into play when
-- trying to reflect the typechecker.
----------------------------------------------------------------------------

module Language.Stitch.LH.Data.Map
  ( module Language.Stitch.LH.Data.Map
  , Map
  )
  where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Prelude hiding (lookup)

-- XXX: put lookup in the logic and use rewrite rules to give it
-- an implementation
-- XXX: GHC only seems to fire rules if the definitions are eta expanded.
{-@
reflect lookup
lazy lookup
lookup
  :: forall <p :: b -> Bool>.
     Ord a
  => k : a
  -> m : Map a b<p>
  -> { r : Maybe b<p>
     | not (Set.member k (mapKeys m)) <=> r = Nothing
     }
@-}
lookup :: Ord a => a -> Map a b -> Maybe b
lookup a m = lookup a m
  where
    _ = Set.empty :: Set () -- quiet warning about unused imports

{-# RULES "lookupImpl" lookup = Map.lookup #-}

{-@
reflect insert
lazy insert
insert
  :: forall <p :: b -> Bool>.
     Ord a
  => a
  -> b<p>

  -> Map a b<p>
  -> Map a b<p>
@-}
insert :: Ord a => a -> b -> Map a b -> Map a b
insert a b m = insert a b m

{-# RULES "insertImpl" insert = Map.insert #-}

{-@
reflect empty
lazy empty
empty :: forall <p :: b -> Bool>. Map a b<p>
@-}
empty :: Map a b
empty = goEmpty ()

-- XXX: Making goEmpty local to empty, causes LH to crash when
-- building Check.hs.
{-@ reflect goEmpty @-}
-- XXX: For some reason, GHC aggrees to fire emptyImpl only if
-- empty appears in an auxiliar definition like this one.
goEmpty :: () -> Map a b
goEmpty () = goEmpty ()

{-# RULES "emptyImpl" goEmpty () = Map.empty #-}


{-@
measure mapKeys :: Map a b -> Set a
@-}
