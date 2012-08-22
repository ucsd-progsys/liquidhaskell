{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__
-- LIQUID {- LANGUAGE DeriveDataTypeable, StandaloneDeriving -}
#endif
#if !defined(TESTING) && __GLASGOW_HASKELL__ >= 703
{-# LANGUAGE Trustworthy #-}
#endif

module Data.Map.Base (Map(..), keys) where

import Prelude hiding (lookup,map,filter,foldr,foldl,null)
import Data.Monoid (Monoid(..))
import Data.Traversable (Traversable(traverse))
import qualified Data.Foldable as Foldable
import Control.DeepSeq (NFData(rnf))

#if __GLASGOW_HASKELL__
import GHC.Exts ( build )
import Text.Read
import Data.Data
#endif

#define STRICT_1_OF_2(fn) fn arg _ | arg `seq` False = undefined
#define STRICT_1_OF_3(fn) fn arg _ _ | arg `seq` False = undefined
#define STRICT_2_OF_3(fn) fn _ arg _ | arg `seq` False = undefined
#define STRICT_1_OF_4(fn) fn arg _ _ _ | arg `seq` False = undefined
#define STRICT_2_OF_4(fn) fn _ arg _ _ | arg `seq` False = undefined

data Map k a  = Bin Size k a (Map k a) (Map k a)
              | Tip

type Size     = Int

{-@ 
  data Map k a <l :: root:k -> k -> Bool, r :: root:k -> k -> Bool>
       = Bin (sz    :: Size) 
             (key   :: k) 
             (value :: a) 
             (left  :: Map <l, r> (k <l key>) a) 
             (right :: Map <l, r> (k <r key>) a) 
       | Tip 
  @-}

{-@ type OMap k a = Map <{v:k | v < root}, {v:k | v > root}> k a @-}


{-@ keys :: OMap k a -> [k]<{v: k | v >= fld}> @-}
keys  :: Map k a -> [k]
-- LIQUID-MANUAL-INLINE keys = foldrWithKey (\k _ ks -> k : ks) []
keys = go [] 
  where
    go z' Tip             = z'
    go z' (Bin _ kx x l r) = go ((\k _ ks -> k : ks) kx x (go z' r)) l 

