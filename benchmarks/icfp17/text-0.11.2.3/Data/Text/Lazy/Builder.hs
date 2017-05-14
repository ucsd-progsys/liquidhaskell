{-@ LIQUID "--pruneunsorted" @-}

{-# LANGUAGE BangPatterns, CPP, Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}

-----------------------------------------------------------------------------
-- |
-- Module      : Data.Text.Lazy.Builder
-- Copyright   : (c) 2010 Johan Tibell
-- License     : BSD3-style (see LICENSE)
--
-- Maintainer  : Johan Tibell <johan.tibell@gmail.com>
-- Stability   : experimental
-- Portability : portable to Hugs and GHC
--
-- Efficient construction of lazy @Text@ values.  The principal
-- operations on a @Builder@ are @singleton@, @fromText@, and
-- @fromLazyText@, which construct new builders, and 'mappend', which
-- concatenates two builders.
--
-- To get maximum performance when building lazy @Text@ values using a builder, associate @mappend@ calls to the right.  For example, prefer
--
-- > singleton 'a' `mappend` (singleton 'b' `mappend` singleton 'c')
--
-- to
--
-- > singleton 'a' `mappend` singleton 'b' `mappend` singleton 'c'
--
-- as the latter associates @mappend@ to the left.
--
-----------------------------------------------------------------------------

module Data.Text.Lazy.Builder
   ( -- * The Builder type
     Builder
   , toLazyText
   , toLazyTextWith

     -- * Constructing Builders
   , singleton
   , fromText
   , fromLazyText
   , fromString

     -- * Flushing the buffer state
   , flush
   ) where

import Control.Monad.ST (ST, runST)
import Data.Bits ((.&.))
import Data.Monoid (Monoid(..))
import Data.Text.Internal (Text(..))
import Data.Text.Lazy.Internal (smallChunkSize)
import Data.Text.Unsafe (inlineInterleaveST)
import Data.Text.UnsafeChar (ord, unsafeWrite)
import Data.Text.UnsafeShift (shiftR)
import Prelude hiding (map, putChar)

import qualified Data.String as String
import qualified Data.Text as S
import qualified Data.Text.Array as A
import qualified Data.Text.Lazy as L


------------------------------------------------------------------------

-- | A @Builder@ is an efficient way to build lazy @Text@ values.
-- There are several functions for constructing builders, but only one
-- to inspect them: to extract any data, you have to turn them into
-- lazy @Text@ values using @toLazyText@.
--
-- Internally, a builder constructs a lazy @Text@ by filling arrays
-- piece by piece.  As each buffer is filled, it is \'popped\' off, to
-- become a new chunk of the resulting lazy @Text@.  All this is
-- hidden from the user of the @Builder@.
--LIQUID FIXME: this was a newtype, but crashed with a `Non-all TyApp` error
data Builder = Builder {
     -- Invariant (from Data.Text.Lazy):
     --      The lists include no null Texts.
     runBuilder :: forall s. (Buffer s -> ST s [S.Text])
                -> Buffer s
                -> ST s [S.Text]
   }

--LIQUID instance Monoid Builder where
--LIQUID    mempty  = empty
--LIQUID    {-# INLINE mempty #-}
--LIQUID    mappend = append
--LIQUID    {-# INLINE mappend #-}
--LIQUID    mconcat = foldr mappend mempty
--LIQUID    {-# INLINE mconcat #-}

--LIQUID instance String.IsString Builder where
--LIQUID     fromString = fromString
--LIQUID     {-# INLINE fromString #-}

instance Show Builder where
    show = show . toLazyText

--LIQUID instance Eq Builder where
--LIQUID     a == b = toLazyText a == toLazyText b
--LIQUID 
--LIQUID instance Ord Builder where
--LIQUID     a <= b = toLazyText a <= toLazyText b

------------------------------------------------------------------------

-- | /O(1)./ The empty @Builder@, satisfying
--
--  * @'toLazyText' 'empty' = 'L.empty'@
--
empty :: Builder
empty = Builder (\ k buf -> k buf)
{-# INLINE empty #-}

-- | /O(1)./ A @Builder@ taking a single character, satisfying
--
--  * @'toLazyText' ('singleton' c) = 'L.singleton' c@
--
singleton :: Char -> Builder
singleton c = writeAtMost 2 $ \ marr o ->
    if n < 0x10000
    then A.unsafeWrite marr o (fromIntegral n) >> return 1
    else do
        A.unsafeWrite marr o lo
        A.unsafeWrite marr (o+1) hi
        return 2
  where n = ord c
        m = n - 0x10000
        lo = fromIntegral $ (m `shiftR` 10) + 0xD800
        hi = fromIntegral $ (m .&. 0x3FF) + 0xDC00
{-# INLINE singleton #-}

------------------------------------------------------------------------

-- | /O(1)./ The concatenation of two builders, an associative
-- operation with identity 'empty', satisfying
--
--  * @'toLazyText' ('append' x y) = 'L.append' ('toLazyText' x) ('toLazyText' y)@
--
append :: Builder -> Builder -> Builder
append (Builder f) (Builder g) = Builder (f . g)
{-# INLINE [0] append #-}

-- TODO: Experiment to find the right threshold.
copyLimit :: Int
copyLimit = 128

-- This function attempts to merge small @Text@ values instead of
-- treating each value as its own chunk.  We may not always want this.

-- | /O(1)./ A @Builder@ taking a 'S.Text', satisfying
--
--  * @'toLazyText' ('fromText' t) = 'L.fromChunks' [t]@
--
fromText :: S.Text -> Builder
fromText t@(Text arr off l)
    | S.null t       = empty
    | l <= copyLimit = writeN l $ \marr o -> A.copyI marr o arr off (l+o)
    | otherwise      = flush `append` mapBuilder (t :)
{-# INLINE [1] fromText #-}

{-# RULES
"fromText/pack" forall s .
        fromText (S.pack s) = fromString s
 #-}


-- | /O(1)./ A Builder taking a @String@, satisfying
--
--  * @'toLazyText' ('fromString' s) = 'L.fromChunks' [S.pack s]@
--
fromString :: String -> Builder
fromString str = Builder $ \k (Buffer p0 o0 u0 l0) ->
        {-@ Decrease loop 1 6 @-}
        {- LIQUID WITNESS -}
    let loop [] !marr !o !u !l _ = k (Buffer marr o u l)
        loop s@(c:cs) marr o u l (d :: Int)
            | l <= 1 = do
                arr <- A.unsafeFreeze marr
                let !t = Text arr o u
                marr' <- A.new chunkSize
                ts <- inlineInterleaveST (loop s marr' 0 0 chunkSize 0)
                return $ t : ts
            | otherwise = do
                n <- unsafeWrite marr (o+u) c
                loop cs marr o (u+n) (l-n) (d+n)
    in loop str p0 o0 u0 l0 (chunkSize-l0)
  where
    chunkSize = smallChunkSize
{-# INLINE fromString #-}

-- | /O(1)./ A @Builder@ taking a lazy @Text@, satisfying
--
--  * @'toLazyText' ('fromLazyText' t) = t@
--
fromLazyText :: L.Text -> Builder
fromLazyText ts = flush `append` mapBuilder (L.toChunks ts ++)
{-# INLINE fromLazyText #-}

------------------------------------------------------------------------

-- Our internal buffer type
data Buffer s = Buffer {-# UNPACK #-} !(A.MArray s)
                       {-# UNPACK #-} !Int  -- offset
                       {-# UNPACK #-} !Int  -- used units
                       {-# UNPACK #-} !Int  -- length left

{-@ data Buffer s = Buffer
        (marr :: A.MArray s)
        (off  :: {v:Nat | v <= (malen marr)})
        (used :: {v:Nat | (off+v) <= (malen marr)})
        (left :: {v:Nat | v = ((malen marr) - off - used)})
  @-}

{-@ qualif MArrayNE(v:A.MArray s): (malen v) >= 2 @-}

{- measure bufUsed :: Buffer s -> Int
    bufUsed (Buffer m o u l) = u
  @-}

{-@ measure bufLeft :: Buffer s -> Int
    bufLeft (Buffer m o u l) = l
  @-}

{-@ qualif BufLeft (v:int, a:A.MArray s, o:int, u:int)
                  : v = (malen(a) - o  - u)
  @-}
{- qualif BufUsed (v:int, a:A.MArray s, o:int, b:Buffer s)
                  : (o + (bufUsed b) + v) <= (malen a)
  @-}

------------------------------------------------------------------------

-- | /O(n)./ Extract a lazy @Text@ from a @Builder@ with a default
-- buffer size.  The construction work takes place if and when the
-- relevant part of the lazy @Text@ is demanded.
toLazyText :: Builder -> L.Text
toLazyText = toLazyTextWith smallChunkSize

-- | /O(n)./ Extract a lazy @Text@ from a @Builder@, using the given
-- size for the initial buffer.  The construction work takes place if
-- and when the relevant part of the lazy @Text@ is demanded.
--
-- If the initial buffer is too small to hold all data, subsequent
-- buffers will be the default buffer size.
{-@ toLazyTextWith :: Nat -> Builder -> L.Text @-}
toLazyTextWith :: Int -> Builder -> L.Text
toLazyTextWith chunkSize m = L.fromChunks (runST $
  newBuffer chunkSize >>= runBuilder (m `append` flush) (const (return [])))

-- | /O(1)./ Pop the strict @Text@ we have constructed so far, if any,
-- yielding a new chunk in the result lazy @Text@.
flush :: Builder
flush = Builder $ \ k buf@(Buffer p o u l) ->
    if u == 0
    then k buf
    else do arr <- A.unsafeFreeze p
            let !b = Buffer p (o+u) 0 l
                !t = Text arr o u
            ts <- inlineInterleaveST (k b)
            return $! t : ts

------------------------------------------------------------------------

-- | Sequence an ST operation on the buffer
withBuffer :: (forall s. Buffer s -> ST s (Buffer s)) -> Builder
withBuffer f = Builder $ \k buf -> f buf >>= k
{-# INLINE withBuffer #-}

-- | Get the size of the buffer
withSize :: (Int -> Builder) -> Builder
withSize f = Builder $ \ k buf@(Buffer _ _ _ l) ->
    runBuilder (f l) k buf
{-# INLINE withSize #-}

-- | Map the resulting list of texts.
mapBuilder :: ([S.Text] -> [S.Text]) -> Builder
mapBuilder f = Builder (fmap f .)

------------------------------------------------------------------------

-- | Ensure that there are at least @n@ many elements available.
ensureFree :: Int -> Builder
ensureFree !n = withSize $ \ l ->
    if n <= l
    then empty
    else flush `append'` withBuffer (const (newBuffer (max n smallChunkSize)))
{-# INLINE [0] ensureFree #-}

{-@ writeAtMost :: n:Nat
                -> (forall s. ma:A.MArray s
                    -> i:{v:Nat | (v+n) <= (malen ma)}
                    -> ST s {v:Nat | v <= n})
                -> Builder
  @-}
writeAtMost :: Int -> (forall s. A.MArray s -> Int -> ST s Int) -> Builder
--LIQUID writeAtMost n f = ensureFree n `append'` withBuffer (writeBuffer f)
writeAtMost n f = Builder $ \ k buf@(Buffer p o u l) ->
                  if n <= l
                  then writeBuffer buf n f >>= k
                  else let write = newBuffer (max n smallChunkSize) >>= \buf' ->
                                   writeBuffer buf' n f >>= k
                       in if u == 0
                          then write
                          else do arr <- A.unsafeFreeze p
                                  let !b = Buffer p (o+u) 0 l
                                      !t = Text arr o u
                                  ts <- inlineInterleaveST write
                                  return $! t : ts
{-# INLINE [0] writeAtMost #-}

-- | Ensure that @n@ many elements are available, and then use @f@ to
-- write some elements into the memory.
{-@ writeN :: n:Nat
           -> (forall s. ma:A.MArray s
               -> i:{v:Nat | (v+n) <= (malen ma)}
               -> ST s ())
           -> Builder
  @-}
writeN :: Int -> (forall s. A.MArray s -> Int -> ST s ()) -> Builder
writeN n f = writeAtMost n (\ p o -> f p o >> return n)
{-# INLINE writeN #-}

--LIQUID writeBuffer :: (A.MArray s -> Int -> ST s Int) -> Buffer s -> ST s (Buffer s)
--LIQUID writeBuffer f (Buffer p o u l) = do
--LIQUID     n <- f p (o+u)
--LIQUID     return $! Buffer p o (u+n) (l-n)
{-@ writeBuffer :: b:Buffer s
                -> n:{v:Nat | v <= (bufLeft b)}
                -> (ma:A.MArray s
                    -> i:{v:Nat | (v+n) <= (malen ma)}
                    -> ST s {v:Nat | v <= n})
                -> ST s (Buffer s)
  @-}
writeBuffer :: Buffer s -> Int -> (A.MArray s -> Int -> ST s Int) -> ST s (Buffer s)
writeBuffer b@(Buffer p o u l) n f = do
    n <- f p (o+u)
    return $! Buffer p o (u+n) (l-n)
{-# INLINE writeBuffer #-}

{-@ newBuffer :: size:Nat
              -> ST s {v:(Buffer s) | size = (bufLeft v)}
  @-}
newBuffer :: Int -> ST s (Buffer s)
newBuffer size = do
    arr <- A.new size
    return $! Buffer arr 0 0 size
{-# INLINE newBuffer #-}

------------------------------------------------------------------------
-- Some nice rules for Builder

-- This function makes GHC understand that 'writeN' and 'ensureFree'
-- are *not* recursive in the precense of the rewrite rules below.
-- This is not needed with GHC 7+.
append' :: Builder -> Builder -> Builder
append' (Builder f) (Builder g) = Builder (f . g)
{-# INLINE append' #-}

{- RULES

"append/writeAtMost" forall a b (f::forall s. A.MArray s -> Int -> ST s Int)
                           (g::forall s. A.MArray s -> Int -> ST s Int) ws.
    append (writeAtMost a f) (append (writeAtMost b g) ws) =
        append (writeAtMost (a+b) (\marr o -> f marr o >>= \ n ->
                                    g marr (o+n) >>= \ m ->
                                    let s = n+m in s `seq` return s)) ws

"writeAtMost/writeAtMost" forall a b (f::forall s. A.MArray s -> Int -> ST s Int)
                           (g::forall s. A.MArray s -> Int -> ST s Int).
    append (writeAtMost a f) (writeAtMost b g) =
        writeAtMost (a+b) (\marr o -> f marr o >>= \ n ->
                            g marr (o+n) >>= \ m ->
                            let s = n+m in s `seq` return s)

"ensureFree/ensureFree" forall a b .
    append (ensureFree a) (ensureFree b) = ensureFree (max a b)

"flush/flush"
    append flush flush = flush

 #-}
