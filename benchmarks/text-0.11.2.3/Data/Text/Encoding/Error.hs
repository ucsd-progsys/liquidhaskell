{-# LANGUAGE CPP, DeriveDataTypeable #-}
-- |
-- Module      : Data.Text.Encoding.Error
-- Copyright   : (c) Bryan O'Sullivan 2009
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : GHC
--
-- Types and functions for dealing with encoding and decoding errors
-- in Unicode text.
--
-- The standard functions for encoding and decoding text are strict,
-- which is to say that they throw exceptions on invalid input.  This
-- is often unhelpful on real world input, so alternative functions
-- exist that accept custom handlers for dealing with invalid inputs.
-- These 'OnError' handlers are normal Haskell functions.  You can use
-- one of the presupplied functions in this module, or you can write a
-- custom handler of your own.

module Data.Text.Encoding.Error
    (
    -- * Error handling types
      UnicodeException(..)
    , OnError
    , OnDecodeError
    , OnEncodeError
    -- * Useful error handling functions
    , lenientDecode
    , strictDecode
    , strictEncode
    , ignore
    , replace
    ) where

#if __GLASGOW_HASKELL__ >= 610
import Control.Exception (Exception, throw)
#else
import Control.Exception.Extensible (Exception, throw)
#endif
import Data.Typeable (Typeable)
import Data.Word (Word8)
import Numeric (showHex)

-- | Function type for handling a coding error.  It is supplied with
-- two inputs:
--
-- * A 'String' that describes the error.
--
-- * The input value that caused the error.  If the error arose
--   because the end of input was reached or could not be identified
--   precisely, this value will be 'Nothing'.
--
-- If the handler returns a value wrapped with 'Just', that value will
-- be used in the output as the replacement for the invalid input.  If
-- it returns 'Nothing', no value will be used in the output.
--
-- Should the handler need to abort processing, it should use 'error'
-- or 'throw' an exception (preferably a 'UnicodeException').  It may
-- use the description provided to construct a more helpful error
-- report.
type OnError a b = String -> Maybe a -> Maybe b

-- | A handler for a decoding error.
type OnDecodeError = OnError Word8 Char

-- | A handler for an encoding error.
type OnEncodeError = OnError Char Word8

-- | An exception type for representing Unicode encoding errors.
data UnicodeException =
    DecodeError String (Maybe Word8)
    -- ^ Could not decode a byte sequence because it was invalid under
    -- the given encoding, or ran out of input in mid-decode.
  | EncodeError String (Maybe Char)
    -- ^ Tried to encode a character that could not be represented
    -- under the given encoding, or ran out of input in mid-encode.
    deriving (Eq, Typeable)

showUnicodeException :: UnicodeException -> String
showUnicodeException (DecodeError desc (Just w))
    = "Cannot decode byte '\\x" ++ showHex w ("': " ++ desc)
showUnicodeException (DecodeError desc Nothing)
    = "Cannot decode input: " ++ desc
showUnicodeException (EncodeError desc (Just c))
    = "Cannot encode character '\\x" ++ showHex (fromEnum c) ("': " ++ desc)
showUnicodeException (EncodeError desc Nothing)
    = "Cannot encode input: " ++ desc

instance Show UnicodeException where
    show = showUnicodeException

instance Exception UnicodeException

-- | Throw a 'UnicodeException' if decoding fails.
strictDecode :: OnDecodeError
strictDecode desc c = throw (DecodeError desc c)

-- | Replace an invalid input byte with the Unicode replacement
-- character U+FFFD.
lenientDecode :: OnDecodeError
lenientDecode _ _ = Just '\xfffd'

-- | Throw a 'UnicodeException' if encoding fails.
strictEncode :: OnEncodeError
strictEncode desc c = throw (EncodeError desc c)

-- | Ignore an invalid input, substituting nothing in the output.
ignore :: OnError a b
ignore _ _ = Nothing

-- | Replace an invalid input with a valid output.
replace :: b -> OnError a b
replace c _ _ = Just c
