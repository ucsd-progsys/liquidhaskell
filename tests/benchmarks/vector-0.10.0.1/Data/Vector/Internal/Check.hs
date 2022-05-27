{-# LANGUAGE CPP #-}

-- |
-- Module      : Data.Vector.Internal.Check
-- Copyright   : (c) Roman Leshchinskiy 2009
-- License     : BSD-style
--
-- Maintainer  : Roman Leshchinskiy <rl@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable
--
-- Bounds checking infrastructure
--

{-# LANGUAGE MagicHash #-}

module Data.Vector.Internal.Check (
  Checks(..), doChecks,

  error, internalError,
  check, checkIndex, checkLength, checkSlice, checkLIQUID, checkIndexLIQUID
) where

import GHC.Base( Int(..) )
import GHC.Prim( Int# )
import Prelude hiding( error, (&&), (||), not )
import qualified Prelude as P

-- NOTE: This is a workaround for GHC's weird behaviour where it doesn't inline
-- these functions into unfoldings which makes the intermediate code size
-- explode. See http://hackage.haskell.org/trac/ghc/ticket/5539.
infixr 2 ||
infixr 3 &&

{-@ not :: b:Bool -> {v:Bool | ((Prop v) <=> ~(Prop b))} @-}
not :: Bool -> Bool
{-# INLINE not #-}
not True = False
not False = True

{-@ (&&) :: x:Bool -> y:Bool -> {v:Bool | ((Prop v) <=> ((Prop x) && (Prop y)))} @-}
(&&) :: Bool -> Bool -> Bool
{-# INLINE (&&) #-}
False && x = False
True && x = x

{-@ (||) :: x:Bool -> y:Bool -> {v:Bool | ((Prop v) <=> ((Prop x) || (Prop y)))} @-}
(||) :: Bool -> Bool -> Bool
{-# INLINE (||) #-}
True || x = True
False || x = x


data Checks = Bounds | Unsafe | Internal deriving( Eq )

doBoundsChecks :: Bool
#ifdef VECTOR_BOUNDS_CHECKS
doBoundsChecks = True
#else
doBoundsChecks = False
#endif

doUnsafeChecks :: Bool
#ifdef VECTOR_UNSAFE_CHECKS
doUnsafeChecks = True
#else
doUnsafeChecks = False
#endif

doInternalChecks :: Bool
#ifdef VECTOR_INTERNAL_CHECKS
doInternalChecks = True
#else
doInternalChecks = False
#endif


doChecks :: Checks -> Bool
{-# INLINE doChecks #-}
doChecks Bounds   = doBoundsChecks
doChecks Unsafe   = doUnsafeChecks
doChecks Internal = doInternalChecks

error_msg :: String -> Int -> String -> String -> String
error_msg file line loc msg = file ++ ":" ++ show line ++ " (" ++ loc ++ "): " ++ msg


{-@ error :: {v:_ | false} -> _ @-}
error :: String -> Int -> String -> String -> a
{-# NOINLINE error #-}
error file line loc msg
  = P.error $ error_msg file line loc msg

{-@ internalError :: {v:_ | false} -> _ @-}
internalError :: String -> Int -> String -> String -> a
{-# NOINLINE internalError #-}
internalError file line loc msg
  = P.error $ unlines
        ["*** Internal error in package vector ***"
        ,"*** Please submit a bug report at http://trac.haskell.org/vector"
        ,error_msg file line loc msg]


{-@ checkError :: {v:_ | false} -> _ @-}
checkError :: String -> Int -> Checks -> String -> String -> a
{-# NOINLINE checkError #-}
checkError file line kind loc msg
  = case kind of
      Internal -> internalError file line loc msg
      _ -> error file line loc msg

{-@ check :: _ -> _ -> _ -> _ -> _ -> {v:Bool | (Prop v)} -> _ -> _ @-}
check :: String -> Int -> Checks -> String -> String -> Bool -> a -> a
{-# INLINE check #-}
check file line kind loc msg cond x
  | not (doChecks kind) || cond = x
  | otherwise = checkError file line kind loc msg


{-@ checkLIQUID :: _ -> _ -> _ -> _ -> _ -> b:Bool -> _ -> {v:_ | (Prop b)} @-}
checkLIQUID :: String -> Int -> Checks -> String -> String -> Bool -> a -> a
{-# INLINE checkLIQUID #-}
checkLIQUID file line kind loc msg cond x
  | not (doChecks kind) || cond = x
  | otherwise = case kind of
                  Internal -> internalError file line loc msg
                  _        -> error file line loc msg

checkIndex_msg :: Int -> Int -> String
{-# INLINE checkIndex_msg #-}
checkIndex_msg (I# i#) (I# n#) = checkIndex_msg# i# n#


checkIndex_msg# :: Int# -> Int# -> String
{-# NOINLINE checkIndex_msg# #-}
checkIndex_msg# i# n# = "index out of bounds " ++ show (I# i#, I# n#)

{-@ checkIndex :: String -> Int -> Checks -> String -> i:Nat -> {n:Nat | i < n } -> a -> a @-}
checkIndex :: String -> Int -> Checks -> String -> Int -> Int -> a -> a
{-# INLINE checkIndex #-}
checkIndex file line kind loc i n x
  = check file line kind loc (checkIndex_msg i n) (i >= 0 && i<n) x


{-@ checkIndexLIQUID :: String -> Int -> Checks -> String -> i:Int -> n:Int -> a -> {v:a | (0 <= i && i < n)} @-}
checkIndexLIQUID :: String -> Int -> Checks -> String -> Int -> Int -> a -> a
{-# INLINE checkIndexLIQUID #-}
checkIndexLIQUID file line kind loc i n x
  = checkLIQUID file line kind loc (checkIndex_msg i n) (i >= 0 && i<n) x


checkLength_msg :: Int -> String
{-# INLINE checkLength_msg #-}
checkLength_msg (I# n#) = checkLength_msg# n#

checkLength_msg# :: Int# -> String
{-# NOINLINE checkLength_msg# #-}
checkLength_msg# n# = "negative length " ++ show (I# n#)

{-@ checkLength :: String -> Int -> Checks -> String -> Nat -> a -> a @-}
checkLength :: String -> Int -> Checks -> String -> Int -> a -> a
{-# INLINE checkLength #-}
checkLength file line kind loc n x
  = check file line kind loc (checkLength_msg n) (n >= 0) x


checkSlice_msg :: Int -> Int -> Int -> String
{-# INLINE checkSlice_msg #-}
checkSlice_msg (I# i#) (I# m#) (I# n#) = checkSlice_msg# i# m# n#

checkSlice_msg# :: Int# -> Int# -> Int# -> String
{-# NOINLINE checkSlice_msg# #-}
checkSlice_msg# i# m# n# = "invalid slice " ++ show (I# i#, I# m#, I# n#)

{-@ checkSlice :: String -> Int -> Checks -> String -> i:Nat -> m:Nat -> {n:Nat | i + m <= n} -> a -> a @-}
checkSlice :: String -> Int -> Checks -> String -> Int -> Int -> Int -> a -> a
{-# INLINE checkSlice #-}
checkSlice file line kind loc i m n x
  = check file line kind loc (checkSlice_msg i m n)
                             (i >= 0 && m >= 0 && i+m <= n) x
