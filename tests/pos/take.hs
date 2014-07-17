{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP,  NoImplicitPrelude, MagicHash #-}
{-# OPTIONS_HADDOCK hide #-}

module Take (
    take0
  , take
  ) where

import Data.Maybe
import GHC.Base 
import Language.Haskell.Liquid.Prelude (liquidAssert, liquidError) 



{-@ assert take0  :: n: {v: Int | 0 <= v} -> [a] -> {v:[a] | (len(v) = n)} @-}
take0 :: Int -> [a] -> [a]
take0 (I# n#) xs = take_unsafe_UInt0 n# xs

take_unsafe_UInt0 :: Int# -> [a] -> [a]
take_unsafe_UInt0 0#  _     = []
take_unsafe_UInt0 n  (x:xs) = x : take_unsafe_UInt0 (n -# 1#) xs
take_unsafe_UInt0 _   _     = error "unsafe take"

{-@ assert take  :: n: {v: Int | v >= 0 } -> xs:[a] -> {v:[a] | len v = if len xs < n then (len xs) else n } @-}
take (I# n#) xs = takeUInt n# xs
-- take (I# n#) xs = take_unsafe_UInt n# xs

takeUInt :: Int# -> [a] -> [a]
takeUInt n xs
  | isTrue# (n >=# 0#) =  take_unsafe_UInt n xs
  | otherwise          =  liquidAssert False []

take_unsafe_UInt :: Int# -> [a] -> [a]
take_unsafe_UInt 0#  _     = []
take_unsafe_UInt n ls      =
  case ls of
    []     -> []
    (x:xs) -> x : take_unsafe_UInt (n -# 1#) xs



















