{--! run liquid with maxparams=3 -}
{-# LANGUAGE CPP, DeriveDataTypeable #-}

-- |
-- Module      : Data.Text.Internal
-- Copyright   : (c) 2008, 2009 Tom Harper,
--               (c) 2009, 2010 Bryan O'Sullivan,
--               (c) 2009 Duncan Coutts
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : GHC
--
-- A module containing private 'Text' internals. This exposes the
-- 'Text' representation and low level construction functions.
-- Modules which extend the 'Text' system may need to use this module.
--
-- You should not use this module unless you are determined to monkey
-- with the internals, as the functions here do just about nothing to
-- preserve data invariants.  You have been warned!

module Data.Text.Internal
    (
    -- * Types
      Text(..)
    -- * Construction
    , text
    , textP
    -- * Safety
    , safe
    -- * Code that must be here for accessibility
    , empty
    -- * Utilities
    , firstf
    -- * Debugging
    , showText
    ) where

--LIQUID #if defined(ASSERTS)
import Control.Exception (assert)
--LIQUID #endif
import Data.Bits ((.&.))
import qualified Data.Text.Array as A
import Data.Text.UnsafeChar (ord)
import Data.Typeable (Typeable)

--LIQUID
import qualified Data.Text.Array
import qualified Data.Word
import Language.Haskell.Liquid.Prelude

{-@ data Data.Text.Internal.Text = Data.Text.Internal.Text
            (arr :: Data.Text.Array.Array)
            (off :: {v:Nat | v <= (alen arr)})
            (len :: {v:Nat | (v + off) <= (alen arr)})
  @-}

{-@ measure tarr :: Data.Text.Internal.Text -> Data.Text.Array.Array
    tarr (Data.Text.Internal.Text a o l) = a
  @-}

{-@ measure toff :: Data.Text.Internal.Text -> Int
    toff (Data.Text.Internal.Text a o l) = o
  @-}

{-@ measure tlen :: Data.Text.Internal.Text -> Int
    tlen (Data.Text.Internal.Text a o l) = l
  @-}

{-@ type NonEmptyStrict = {v:Data.Text.Internal.Text | (tlen v) > 0} @-}

{-@ qualif NonEmptyText(v:Data.Text.Internal.Text): tlen(v) > 0 @-}
{-@ qualif NonEmptyText(v:Data.Text.Internal.Text): tlength(v) > 0 @-}

{-@ measure sum_tlens :: [Data.Text.Internal.Text] -> Int
    sum_tlens ([]) = 0
    sum_tlens (t:ts) = (tlen t) + (sum_tlens ts)
  @-}

{-@ measure tlength :: Data.Text.Internal.Text -> Int
    tlength (Data.Text.Internal.Text a o l) = numchars(a,o,l)
  @-}

{-@ qualif TLengthEq(v:Data.Text.Internal.Text, t:Data.Text.Internal.Text):
        tlength(v) = tlength(t)
  @-}
{-@ qualif TLengthLe(v:Data.Text.Internal.Text, t:Data.Text.Internal.Text):
        tlength(v) <= tlength(t)
  @-}

{-@ qualif MinTLength(v:Data.Text.Internal.Text, n:Int, t:Data.Text.Internal.Text):
        tlength(v) = (tlength(t) > n ? n : tlength(t))
  @-}

{-@ qualif TLengthAcc(v:int, t:Data.Text.Internal.Text, l:int):
        v = ((tlength t) + l)
  @-}

{-@ qualif TLengthDiff(v:Data.Text.Internal.Text,
                       t1:Data.Text.Internal.Text,
                       t2:Data.Text.Internal.Text):
        tlength(v) = tlength(t1) - tlength(t2)
  @-}

{-@ measure sum_tlengths :: [Data.Text.Internal.Text] -> Int
    sum_tlengths ([]) = 0
    sum_tlengths (t:ts) = (tlength t) + (sum_tlengths ts)
  @-}

{-@ invariant {v:Data.Text.Internal.Text | (numchars (tarr v) (toff v) 0) = 0} @-}
{-@ invariant {v:Data.Text.Internal.Text | (numchars (tarr v) (toff v) (tlen v)) >= 0} @-}
{-@ invariant {v:Data.Text.Internal.Text | (numchars (tarr v) (toff v) (tlen v)) <= (tlen v)} @-}

{-@ invariant {v:Data.Text.Internal.Text | (((tlength v) = 0) <=> ((tlen v) = 0))} @-}
{-@ invariant {v:Data.Text.Internal.Text | (tlength v) >= 0} @-}
{-@ invariant {v:Data.Text.Internal.Text | (tlength v) = (numchars (tarr v) (toff v) (tlen v))} @-}

{-@ invariant {v:[Data.Text.Internal.Text] | (sum_tlens v) >= 0} @-}
{-@ invariant {v:[{v0:Data.Text.Internal.Text |
                  ((((len v) > 1) && ((tlen v0) > 0)) => ((tlen v0) < (sum_tlens v)))}] | true} @-}
{-@ invariant {v:[{v0:Data.Text.Internal.Text |
               ((((tlen v0) > 0) && (((len v) > 0))) => ((sum_tlens v) > 0))}] | true} @-}

-- | A space efficient, packed, unboxed Unicode text type.
data Text = Text
    {-# UNPACK #-} !A.Array          -- payload
    {-# UNPACK #-} !Int              -- offset
    {-# UNPACK #-} !Int              -- length
--LIQUID    deriving (Typeable)

-- | Smart constructor.
{-@ text :: a:Data.Text.Array.Array
         -> o:{v:Nat | v <= (alen a)}
         -> l:{v:Nat | (v+o) <= (alen a)}
         -> {v:Text | (((tarr v) = a) && ((toff v) = o) && ((tlen v) = l)
                       && ((tlength v) = (numchars a o l)))}
  @-}
text :: A.Array -> Int -> Int -> Text
text arr off len =
--LIQUID pushing bindings inward to prove safety
--LIQUID #if defined(ASSERTS)
--LIQUID  let c    = A.unsafeIndex arr off
--LIQUID      alen = A.length arr
  let alen = A.aLen arr
  in liquidAssert (len >= 0) .
     liquidAssert (off >= 0) .
     liquidAssert (alen == 0 || len == 0 || off < alen) $
--LIQUID     assert (len == 0 || c < 0xDC00 || c > 0xDFFF) $
     let t = if len == 0 then Text arr off len else
                let c = A.unsafeIndex arr off in
                assert (c < 0xDC00 || c > 0xDFFF) $
--LIQUID #endif
                Text arr off len
     in liquidAssume (tlEqNumchars t arr off len) t
{-# INLINE text #-}

-- | /O(1)/ The empty 'Text'.
{-@ empty :: {v:Data.Text.Internal.Text | (tlen v) = 0} @-}
empty :: Text
empty = Text A.empty 0 0
{-# INLINE [1] empty #-}

-- | Construct a 'Text' without invisibly pinning its byte array in
-- memory if its length has dwindled to zero.
{-@ textP :: a:Data.Text.Array.Array
          -> o:{v:Nat | v <= (alen a)}
          -> l:{v:Nat | (v+o) <= (alen a)}
          -> {v:Data.Text.Internal.Text | (((tlen v) = l) && ((tlength v) = (numchars a o l)))}
  @-}
textP :: A.Array -> Int -> Int -> Text
textP arr off len | len == 0  = liquidAssume (numcharsZ arr off len) empty
                  | otherwise = text arr off len
{-# INLINE textP #-}

-- | A useful 'show'-like function for debugging purposes.
showText :: Text -> String
showText (Text arr off len) =
    "Text " ++ show (A.toList arr off len) ++ ' ' :
            show off ++ ' ' : show len

-- | Map a 'Char' to a 'Text'-safe value.
--
-- UTF-16 surrogate code points are not included in the set of Unicode
-- scalar values, but are unfortunately admitted as valid 'Char'
-- values by Haskell.  They cannot be represented in a 'Text'.  This
-- function remaps those code points to the Unicode replacement
-- character \"&#xfffd;\", and leaves other code points unchanged.
safe :: Char -> Char
safe c
    | ord c .&. 0x1ff800 /= 0xd800 = c
    | otherwise                    = '\xfffd'
{-# INLINE safe #-}

-- | Apply a function to the first element of an optional pair.
firstf :: (a -> c) -> Maybe (a,b) -> Maybe (c,b)
firstf f (Just (a, b)) = Just (f a, b)
firstf _  Nothing      = Nothing


--LIQUID
{-@ tlEqNumchars :: t:Data.Text.Internal.Text
                 -> a:Data.Text.Array.Array
                 -> o:Int
                 -> l:Int
                 -> {v:Bool | ((Prop v) <=> ((tlength t) = (numchars a o l)))}
  @-}
tlEqNumchars :: Text -> A.Array -> Int -> Int -> Bool
tlEqNumchars = undefined

{-@ numcharsZ :: a:A.Array -> o:Int -> l:Int
              -> {v:Bool | ((Prop v) <=> ((numchars a o l) = 0))}
  @-}
numcharsZ :: A.Array -> Int -> Int -> Bool
numcharsZ = undefined
