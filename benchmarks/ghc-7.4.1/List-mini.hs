{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP, MagicHash #-}
{-# OPTIONS_HADDOCK hide #-}

-- NoImplicitPrelude

module GHC.List (
 foo, mtake
 ) where

import Data.Maybe
import GHC.Base hiding (assert) 
import Language.Haskell.Liquid.Prelude (liquidAssert, liquidError) 

{-@ assert mtake  :: n: {v: Int | 0 <= v} -> [a] -> {v:[a] | (len(v) = n)} @-}
mtake          :: Int -> [a] -> [a]
-- OK mtake n xs = if n == 0 then [] else case xs of z:zs -> z : mtake (n-1) zs

mtake 0 _      = []
mtake n (x:xs) = x : (mtake ((liquidAssert (n /= 0) n) - 1) xs)
--OK: mtake n (x:xs) = x : (take (n-1) xs)

{- assert take  :: n: {v: Int | v >= 0 } -> xs:[a] -> {v:[a] | len(v) = ((len(xs) < n) ? len(xs) : n) } @-}

{-@ assert foo :: Int -> Int @-}
foo :: Int -> Int
foo 0 = 0
foo n = liquidAssert (n /= 0) (n - 1)

{- INLINE [0] take -}
--take            :: Int -> [a] -> [a]
--take (I# n#) xs = take_unsafe_UInt n# xs
---- take (I# n#) xs = takeUInt n# xs
--
----takeUInt :: Int# -> [a] -> [a]
----takeUInt n xs
----  | n >=# 0#  =  take_unsafe_UInt n xs
----  | otherwise =  liquidAssert False []
--
--take_unsafe_UInt :: Int# -> [a] -> [a]
--take_unsafe_UInt 0#  _     = []
--take_unsafe_UInt n ls      =
--  case ls of
--    -- []     -> []
--    (x:xs) -> x : take_unsafe_UInt (n -# 1#) xs




















