{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE BangPatterns, MagicHash, CPP #-}
-- |
-- Module      : Data.Text.Lazy
-- Copyright   : (c) 2009, 2010, 2012 Bryan O'Sullivan
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : GHC
--
-- A time and space-efficient implementation of Unicode text using
-- lists of packed arrays.
--
-- /Note/: Read below the synopsis for important notes on the use of
-- this module.
--
-- The representation used by this module is suitable for high
-- performance use and for streaming large quantities of data.  It
-- provides a means to manipulate a large body of text without
-- requiring that the entire content be resident in memory.
--
-- Some operations, such as 'concat', 'append', 'reverse' and 'cons',
-- have better time complexity than their "Data.Text" equivalents, due
-- to the underlying representation being a list of chunks. For other
-- operations, lazy 'Text's are usually within a few percent of strict
-- ones, but often with better heap usage if used in a streaming
-- fashion. For data larger than available memory, or if you have
-- tight memory constraints, this module will be the only option.
--
-- This module is intended to be imported @qualified@, to avoid name
-- clashes with "Prelude" functions.  eg.
--
-- > import qualified Data.Text.Lazy as L

module Data.Text.Lazy  where

import Prelude (Char, Bool(..), Maybe(..), String,
                Eq(..), Ord(..), Ordering(..), Read(..), Show(..),
                (&&), (||), (+), (-), (.), ($), (++),
                div, error, flip, fmap, fromIntegral, not, otherwise
               -- LIQUID
               , Num(..), Integral(..), Integer)
import qualified Prelude as P
#if defined(HAVE_DEEPSEQ)
import Control.DeepSeq (NFData(..))
#endif
import Data.Int (Int64)
import qualified Data.List as L
import Data.Char (isSpace)
import Data.Data (Data(gfoldl, toConstr, gunfold, dataTypeOf))
#if __GLASGOW_HASKELL__ >= 612
import Data.Data (mkNoRepType)
#else
import Data.Data (mkNorepType)
#endif
import Data.Monoid (Monoid(..))
import Data.String (IsString(..))
import qualified Data.Text as T
import qualified Data.Text.Internal as T
import qualified Data.Text.Fusion.Common as S
import qualified Data.Text.Unsafe as T
import qualified Data.Text.Lazy.Fusion as S
import Data.Text.Fusion.Internal (PairS(..))
import Data.Text.Lazy.Fusion (stream, unstream)
import Data.Text.Lazy.Internal (Text(..), chunk, empty, foldlChunks, foldrChunks)
import Data.Text.Internal (firstf, safe, textP)
import qualified Data.Text.Util as U
import Data.Text.Lazy.Search (indices)
#if __GLASGOW_HASKELL__ >= 702
import qualified GHC.CString as GHC
#else
import qualified GHC.Base as GHC
#endif
import GHC.Prim (Addr#)

--LIQUID
import Data.Int
import qualified Data.Word
--import qualified Data.Text
import qualified Data.Text.Array
import qualified Data.Text.Fusion.Internal
import qualified Data.Text.Internal
import qualified Data.Text.Lazy.Internal
import qualified Data.Text.Search
import qualified Data.Text.Unsafe
import qualified GHC.Real
import Language.Haskell.Liquid.Prelude

--LIQUID copied from Data.Text.Unsafe
data Iter = Iter {-# UNPACK #-} !Char {-# UNPACK #-} !Int

{-@ data Data.Text.Lazy.Iter = Data.Text.Lazy.Iter (c::Char) (i::Int) @-}

{-@ measure iter_dL :: Data.Text.Lazy.Iter -> Int
    iter_dL (Data.Text.Lazy.Iter c d) = d
  @-}

{-@ assume iter :: t:Data.Text.Internal.Text -> i:{v:Int | (Btwn v 0 (tlen t))}
                -> {v:Data.Text.Lazy.Iter | ((BtwnEI ((iter_dL v)+i) i (tlen t))
                          && ((numchars (tarr t) (toff t) (i+(iter_dL v)))
                              = (1 + (numchars (tarr t) (toff t) i)))
                          && ((numchars (tarr t) (toff t) (i+(iter_dL v)))
                              <= (tlength t)))}
  @-}
iter :: T.Text -> Int -> Iter
iter = P.undefined

{-@ iter_d :: i:Data.Text.Lazy.Iter -> {v:Int | v = (iter_dL i)} @-}
iter_d (Iter c d) = d
--LIQUID end of copied defs


-- $fusion
--
-- Most of the functions in this module are subject to /fusion/,
-- meaning that a pipeline of such functions will usually allocate at
-- most one 'Text' value.
--
-- As an example, consider the following pipeline:
--
-- > import Data.Text.Lazy as T
-- > import Data.Text.Lazy.Encoding as E
-- > import Data.ByteString.Lazy (ByteString)
-- >
-- > countChars :: ByteString -> Int
-- > countChars = T.length . T.toUpper . E.decodeUtf8
--
-- From the type signatures involved, this looks like it should
-- allocate one 'ByteString' value, and two 'Text' values. However,
-- when a module is compiled with optimisation enabled under GHC, the
-- two intermediate 'Text' values will be optimised away, and the
-- function will be compiled down to a single loop over the source
-- 'ByteString'.
--
-- Functions that can be fused by the compiler are documented with the
-- phrase \"Subject to fusion\".

-- $replacement
--
-- A 'Text' value is a sequence of Unicode scalar values, as defined
-- in &#xa7;3.9, definition D76 of the Unicode 5.2 standard:
-- <http://www.unicode.org/versions/Unicode5.2.0/ch03.pdf#page=35>. As
-- such, a 'Text' cannot contain values in the range U+D800 to U+DFFF
-- inclusive. Haskell implementations admit all Unicode code points
-- (&#xa7;3.4, definition D10) as 'Char' values, including code points
-- from this invalid range.  This means that there are some 'Char'
-- values that are not valid Unicode scalar values, and the functions
-- in this module must handle those cases.
--
-- Within this module, many functions construct a 'Text' from one or
-- more 'Char' values. Those functions will substitute 'Char' values
-- that are not valid Unicode scalar values with the replacement
-- character \"&#xfffd;\" (U+FFFD).  Functions that perform this
-- inspection and replacement are documented with the phrase
-- \"Performs replacement on invalid scalar values\".
--
-- (One reason for this policy of replacement is that internally, a
-- 'Text' value is represented as packed UTF-16 data. Values in the
-- range U+D800 through U+DFFF are used by UTF-16 to denote surrogate
-- code points, and so cannot be represented. The functions replace
-- invalid scalar values, instead of dropping them, as a security
-- measure. For details, see Unicode Technical Report 36, &#xa7;3.5:
-- <http://unicode.org/reports/tr36#Deletion_of_Noncharacters>)

{-@ equal :: Data.Text.Lazy.Internal.Text
          -> Data.Text.Lazy.Internal.Text
          -> Bool
  @-}
equal :: Text -> Text -> Bool
equal Empty Empty = True
equal Empty _     = False
equal _ Empty     = False
equal (Chunk a as) (Chunk b bs) =
    case compare lenA lenB of
      LT -> a == (T.takeWord16 lenA b) &&
            as `equal` Chunk (T.dropWord16 lenA b) bs
      EQ -> a == b && as `equal` bs
      GT -> T.takeWord16 lenB a == b &&
            Chunk (T.dropWord16 lenB a) as `equal` bs
  where lenA = T.lengthWord16 a
        lenB = T.lengthWord16 b

instance Eq Text where
    (==) = equal
    {-# INLINE (==) #-}

instance Ord Text where
    compare = compareText

{-@ compareText :: Data.Text.Lazy.Internal.Text
                -> Data.Text.Lazy.Internal.Text
                -> Ordering
  @-}
compareText :: Text -> Text -> Ordering
compareText Empty Empty = EQ
compareText Empty _     = LT
compareText _     Empty = GT
compareText a@(Chunk a0 as) b@(Chunk b0 bs) = compareText_go a0 b0 as bs 0 0 --LIQUID outer a0 b0
--LIQUID  where
--LIQUID   outer ta@(T.Text arrA offA lenA) tb@(T.Text arrB offB lenB) = go 0 0
--LIQUID    where
--LIQUID     go !i !j
--LIQUID       | i >= lenA = compareText as (chunk (T.Text arrB (offB+j) (lenB-j)) bs)
--LIQUID       | j >= lenB = compareText (chunk (T.Text arrA (offA+i) (lenA-i)) as) bs
--LIQUID       | a < b     = LT
--LIQUID       | a > b     = GT
--LIQUID       | otherwise = go (i+di) (j+dj)
--LIQUID       where T.Iter a di = T.iter ta i
--LIQUID             T.Iter b dj = T.iter tb j

{-@ compareText_go :: ta:{v:Data.Text.Internal.Text | (tlength v) > 0}
                   -> tb:{v:Data.Text.Internal.Text | (tlength v) > 0}
                   -> as:Data.Text.Lazy.Internal.Text
                   -> bs:Data.Text.Lazy.Internal.Text
                   -> i:{v:Int | (BtwnI v 0 (tlen ta))}
                   -> j:{v:Int | (BtwnI v 0 (tlen tb))}
                   -> Ordering
  @-}
compareText_go :: T.Text -> T.Text -> Text -> Text -> Int -> Int -> Ordering
compareText_go ta@(T.Text arrA offA lenA) tb@(T.Text arrB offB lenB) as bs !i !j
    | i >= lenA = compareText as (chunk (T.Text arrB (offB+j) (lenB-j)) bs)
    | j >= lenB = compareText (chunk (T.Text arrA (offA+i) (lenA-i)) as) bs
    | otherwise = let ia@(Iter a di) = iter ta i
                      ib@(Iter b dj) = iter tb j
                  in if a < b then LT
                     else if a > b then GT
                     else compareText_go ta tb as bs (i+di) (j+dj)


{-@ null :: t:Data.Text.Lazy.Internal.Text
         -> {v:Bool | ((Prop v) <=> ((ltlength t) = 0))}
  @-}
null :: Text -> Bool
null Empty = True
null _     = False
{-# INLINE [1] null #-}

{-@ isSingleton :: t:Data.Text.Lazy.Internal.Text
                -> {v:Bool | ((Prop v) <=> ((ltlength t) = 1))}
  @-}
isSingleton :: Text -> Bool
--LIQUID isSingleton = S.isSingleton . stream
isSingleton t = P.undefined
{-# INLINE isSingleton #-}

{-@ singleton :: Char -> {v:Data.Text.Lazy.Internal.Text | (ltlength v) = 1} @-}
singleton :: Char -> Text
singleton c = Chunk (T.singleton c) Empty
{-# INLINE [1] singleton #-}

-- | /O(1)/ Returns the first character of a 'Text', which must be
-- non-empty.  Subject to fusion.
{-@ head :: {v:Data.Text.Lazy.Internal.Text | (ltlength v) > 0}
         -> Char
  @-}
head :: Text -> Char
head t = P.undefined
{-# INLINE head #-}

{-@ inits :: t:Data.Text.Lazy.Internal.Text
          -> [{v:Data.Text.Lazy.Internal.Text |
               (BtwnI (ltlength v) 0 (ltlength t))}]<{\hd tl ->
              ((ltlength hd) < (ltlength tl))}>
  @-}
inits :: Text -> [Text]
inits t = Empty : inits' t
--LIQUID inits = (Empty :) . inits'
--LIQUID   where inits' Empty        = []
--LIQUID         inits' (Chunk t ts) = L.map (\t' -> Chunk t' Empty) (L.tail (T.inits t))
--LIQUID                            ++ L.map (Chunk t) (inits' ts)

{-@ inits' :: t:Data.Text.Lazy.Internal.Text
          -> [{v:Data.Text.Lazy.Internal.Text |
               (BtwnEI (ltlength v) 0 (ltlength t))}]<{\hd tl ->
              ((ltlength hd) < (ltlength tl))}>
  @-}
inits' :: Text -> [Text]
inits' Empty           = []
inits' t0@(Chunk t ts) = let (t':ts') = T.inits t
                             lts  = inits_map1 t t' ts'
                             lts' = inits_map2 t0 t (inits' ts)
                         in inits_app t lts t0 lts'

{-@ inits_map1 :: t0:NonEmptyStrict
        -> t:Data.Text.Internal.Text
        -> ts:[{v:Data.Text.Internal.Text | (BtwnEI (tlength v) (tlength t) (tlength t0))}]<{\xx xy -> ((tlength xx) < (tlength xy))}>
        -> [{v:Data.Text.Lazy.Internal.Text | (BtwnEI (ltlength v) (tlength t) (tlength t0))}]<{\lx ly -> ((ltlength lx) < (ltlength ly))}>
  @-}
inits_map1 :: T.Text -> T.Text -> [T.Text] -> [Text]
inits_map1 _  _ []     = []
inits_map1 t0 _ (t:ts) = Chunk t Empty : inits_map1 t0 t ts

{-@ inits_map2 :: t0:Data.Text.Lazy.Internal.Text
        -> st:NonEmptyStrict
        -> ts:[{v:Data.Text.Lazy.Internal.Text | (BtwnEI (ltlength v) 0 ((ltlength t0) - (tlength st)))}]<{\fx fy -> ((ltlength fx) < (ltlength fy))}>
        -> [{v:Data.Text.Lazy.Internal.Text | (BtwnEI (ltlength v) (tlength st) (ltlength t0))}]<{\rx ry -> ((ltlength rx) < (ltlength ry))}>
  @-}
inits_map2 :: Text -> T.Text -> [Text] -> [Text]
inits_map2 _  _  []     = []
inits_map2 t0 st (t:ts) = inits_map2' t0 st t ts

{-@ inits_map2' :: t0:Data.Text.Lazy.Internal.Text
        -> st:NonEmptyStrict
        -> t:Data.Text.Lazy.Internal.Text
        -> ts:[{v:Data.Text.Lazy.Internal.Text | (BtwnEI (ltlength v) (ltlength t) ((ltlength t0) - (tlength st)))}]<{\ax ay -> ((ltlength ax) < (ltlength ay))}>
        -> [{v:Data.Text.Lazy.Internal.Text | (BtwnEI (ltlength v) ((tlength st) + (ltlength t)) (ltlength t0))}]<{\bx by -> ((ltlength bx) < (ltlength by))}>
  @-}
inits_map2' :: Text -> T.Text -> Text -> [Text] -> [Text]
inits_map2' _  _  _ []     = []
inits_map2' t0 st _ (t:ts) = Chunk st t : inits_map2' t0 st t ts


{-@ inits_app :: t:NonEmptyStrict
        -> as:[{v:Data.Text.Lazy.Internal.Text | (ltlength v) <= (tlength t)}]<{\cx cy -> ((ltlength cx) < (ltlength cy))}>
        -> t0:{v:Data.Text.Lazy.Internal.Text | (ltlength v) >= (tlength t)}
        -> bs:[{v:Data.Text.Lazy.Internal.Text | (BtwnEI (ltlength v) (tlength t) (ltlength t0))}]<{\dx dy -> ((ltlength dx) < (ltlength dy))}>
        -> [{v:Data.Text.Lazy.Internal.Text | (BtwnEI (ltlength v) 0 (ltlength t0))}]<{\ex ey -> ((ltlength ex) < (ltlength ey))}>
  @-}
inits_app :: T.Text -> [Text] -> Text -> [Text] -> [Text]
inits_app _ []     _  b = b
inits_app t (a:as) t0 b = inits_app' t a as t0 b

{-@ inits_app' :: t:NonEmptyStrict
        -> a:{v:Data.Text.Lazy.Internal.Text | (ltlength v) <= (tlength t)}
        -> as:[{v:Data.Text.Lazy.Internal.Text | (BtwnEI (ltlength v) (ltlength a) (tlength t))}]<{\cx cy -> ((ltlength cx) < (ltlength cy))}>
        -> t0:{v:Data.Text.Lazy.Internal.Text | (ltlength v) >= (tlength t)}
        -> bs:[{v:Data.Text.Lazy.Internal.Text | (BtwnEI (ltlength v) (tlength t) (ltlength t0))}]<{\dx dy -> ((ltlength dx) < (ltlength dy))}>
        -> [{v:Data.Text.Lazy.Internal.Text | (BtwnEI (ltlength v) (ltlength a) (ltlength t0))}]<{\ex ey -> ((ltlength ex) < (ltlength ey))}>
  @-}
inits_app' :: T.Text -> Text -> [Text] -> Text -> [Text] -> [Text]
inits_app' _ _ []     _  b = b
inits_app' t _ (a:as) t0 b = a : inits_app' t a as t0 b

{- length :: t:Data.Text.Lazy.Internal.Text
           -> {v:Int64 | v = (ltlength t)}
  @-}
length :: Text -> Int64
length t = 1 --P.id $ foldlChunks t go 0 t
  where go l t = l + fromIntegral (T.length t)
-- length = foldlChunks go 0
--     where go l t = l + fromIntegral (T.length t)

-- | /O(c)/ Convert a list of strict 'T.Text's into a lazy 'Text'.
{- fromChunks :: ts:[Data.Text.Internal.Text]
               -> {v:Data.Text.Lazy.Internal.Text | (ltlength v) = (sum_tlengths ts)}
  @-}
-- fromChunks :: [T.Text] -> Text
-- fromChunks cs = L.foldr chunk Empty cs

-- | /O(n)/ Convert a lazy 'Text' into a list of strict 'T.Text's.
{- toChunks :: t:Data.Text.Lazy.Internal.Text
             -> {v:[Data.Text.Internal.Text] | (sum_tlengths v) = (ltlength t)}
  @-}
-- toChunks :: Text -> [T.Text]
-- toChunks cs = foldrChunks (\ts' t ts -> t:ts) [] cs
