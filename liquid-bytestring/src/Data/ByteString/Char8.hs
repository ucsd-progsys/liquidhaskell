{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE Trustworthy #-}
module Data.ByteString.Char8 ( module Exports ) where

import Data.Int
import GHC.IO.Handle


#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_bytestring(0,10,12)

-- bytestring >= 0.10.12.0 is now exporting 'partition' as part of 'Data.ByteString.Char8', which means
-- that we have to use CPP here to refine its type, or we would get a failure like in test \"T1078\".

import Data.ByteString hiding (partition)

{-@

assume partition :: (Char -> GHC.Types.Bool)
                 -> i : Data.ByteString.ByteString
                 -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
                    , { r : Data.ByteString.ByteString | bslen r <= bslen i }
                    )
@-}

#else
import Data.ByteString
#endif
#endif

import "bytestring" Data.ByteString.Char8 as Exports
