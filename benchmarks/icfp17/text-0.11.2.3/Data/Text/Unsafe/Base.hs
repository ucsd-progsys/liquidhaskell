{-# LANGUAGE CPP, MagicHash, UnboxedTuples #-}
-- |
-- Module      : Data.Text.Unsafe.Base
-- Copyright   : (c) 2009, 2010, 2011 Bryan O'Sullivan
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : portable
--
-- A module containing unsafe operations, for very very careful use in
-- heavily tested code.
module Data.Text.Unsafe.Base
    (
      inlineInterleaveST
    , inlinePerformIO
    ) where

import GHC.ST (ST(..))
#if defined(__GLASGOW_HASKELL__)
# if __GLASGOW_HASKELL__ >= 611
import GHC.IO (IO(IO))
# else
import GHC.IOBase (IO(IO))
# endif
import GHC.Base (realWorld#)
#endif


-- | Just like unsafePerformIO, but we inline it. Big performance gains as
-- it exposes lots of things to further inlining. /Very unsafe/. In
-- particular, you should do no memory allocation inside an
-- 'inlinePerformIO' block. On Hugs this is just @unsafePerformIO@.
--
{-# INLINE inlinePerformIO #-}
inlinePerformIO :: IO a -> a
#if defined(__GLASGOW_HASKELL__)
inlinePerformIO (IO m) = case m realWorld# of (# _, r #) -> r
#else
inlinePerformIO = unsafePerformIO
#endif

-- | Allow an 'ST' computation to be deferred lazily. When passed an
-- action of type 'ST' @s@ @a@, the action will only be performed when
-- the value of @a@ is demanded.
--
-- This function is identical to the normal unsafeInterleaveST, but is
-- inlined and hence faster.
--
-- /Note/: This operation is highly unsafe, as it can introduce
-- externally visible non-determinism into an 'ST' action.
inlineInterleaveST :: ST s a -> ST s a
inlineInterleaveST (ST m) = ST $ \ s ->
    let r = case m s of (# _, res #) -> res in (# s, r #)
{-# INLINE inlineInterleaveST #-}
