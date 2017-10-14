{-

This code implements a Monoid for string matching; i.e. a data
structure, MatchIdxs, which has the result of a string match function
plus a little extra information for monoidally combining things
together; the purpose of course is to parallelize string matching
computations. This is the original version I wrote which uses type
level strings to guarantee that only computations done with the same
target string are combinable.

The invariants I'd like to prove are in the comments on the MatchIdxs
constructors. I'd be interested in a way to do it directly with this
code (though it seems that would require extending LH), or doing it in
a version of this code where the constructors have an extra argument
with the value of the target-- however that formulation seems to raise
issues about forcing those values to be the same.

I have a version of the code lying around which tries this approach,
but I couldn't get it to work. I chose to send this version first so
you have the chance to see where I started; I could send you my version
with the explicit terms if you like.

If this goes well, then there are a couple of further things to think
about:

  1) I have another Monoid construction for actual splitting, but
     I don't think LH can handle the invariants as they require an
     isInfixOf operation; but I could be wrong about what LH can do.

  2) It would be interesting to think about whether one can encode
     correctness, rather than just some invariants. By correctness
     I mean both that the monoid laws are satisfied, and that there
     is a homomorphic-like property to the effect of:

     match (x <> y) == match x <> match y

Let me know if you have any questions about the code, or need more
comments/explanation.
-}


{- LIQUID "--diff" @-}
{-@ LIQUID "--scrape-used-imports" @-}
{-@ LIQUID "--short-names" @-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module MatchIdxs where

import qualified Data.ByteString as BS
-- RJ import qualified Data.ByteString.Search as BS
import Data.Char
-- RJ import Data.List.Split(chunksOf)

import Data.Monoid
import Data.Proxy
import Debug.Trace
import GHC.TypeLits

import Language.Haskell.Liquid.Prelude (liquidAssert)
import Prelude hiding (head, min, max)

junk = BS.head


traceMsg msg x = trace (msg ++ show x) x

{-@ chunksBS :: Int -> b:BS.ByteString -> [BS.ByteString] / [(bLength b)] @-}
chunksBS n' xs | BS.null xs = []
               | otherwise = x : chunksBS n xs'
    where (x,xs') = BS.splitAt  (liquidAssert (n > 0) n) xs
          n       = max 1 n'

bsToString :: BS.ByteString -> String
bsToString = map (chr . fromIntegral) . BS.unpack

stringToBS :: String -> BS.ByteString
stringToBS = BS.pack . map (fromIntegral . ord)

-- | get the (proxied and existentially boxed) type level Symbol for a bytestring
someSymbolValBS :: BS.ByteString -> SomeSymbol
someSymbolValBS = someSymbolVal . bsToString

-- | get the bytestring corresponding to a type level Symbol
mkTarg :: forall t . KnownSymbol t => Proxy t -> BS.ByteString
mkTarg = stringToBS . symbolVal


-- | Naive specification of string matching (from Bird)
{-@ indicesSpec :: t:ByteStringNE -> s:BS.ByteString -> [OkPos t s] @-}
-- indicesSpec targ = map ((BS.length targ -) . BS.length) . filter (targ `BS.isSuffixOf`) . BS.inits
indicesSpec targ s = [ BS.length s' - BS.length targ | s' <- BS.inits s
                                                     , targ `BS.isSuffixOf` s' ]

indicesSpec :: BS.ByteString -> BS.ByteString -> [Int]



-- | Datatype to name string matching algorithms; will use it's lifted
-- version put choice in type.
data Alg = BM  -- ^ Boyer-Moore from stringsearch package
         | Spec  -- ^ Naive spec

{-@ indices :: Alg -> t:ByteStringNE -> s:BS.ByteString -> [OkPos t s] @-}
indices BM   = assumeIndices -- RJ BS.indices
indices Spec = indicesSpec


-- | Monoid
--
-- 'MatchIdxs alg targ' denotes the result of running string matching
-- algorithm 'alg' search for target 'targ' in some input. In addition
-- to the match indices, information needed to combine this result
-- with similar results on input to the left and right are also
-- included.
--
-- We'd like to prove that the invariants in the comments hold (|x|
-- denotes the length of x).
data MatchIdxs
    = Small { targ :: BS.ByteString
            , bs   :: BS.ByteString
            }
    | MatchIdxs { targ    :: BS.ByteString
                , input   :: Int
                , left    :: BS.ByteString
                , matches :: [Int]
                , right   :: BS.ByteString
                }
  deriving (Eq, Show)

{-@ data MatchIdxs
      = Small { targ    :: ByteStringNE
              , bs      :: {b:BS.ByteString | bLength b < bLength targ}
              }

      | MatchIdxs
              { targ    :: ByteStringNE
              , input   :: {i  : Int | i >= bLength targ}
              , left    :: {l  : BS.ByteString | bLength l == bLength targ - 1}
              , matches :: [{v : Int | v <= input - bLength targ}]
              , right   :: {r  : BS.ByteString | bLength r == bLength targ - 1}
              }
  @-}


matchIdxsIs :: MatchIdxs -> [Int]
matchIdxsIs (Small _ _) = []
matchIdxsIs (MatchIdxs _ _ _ is _) = is

-- | create a 'MatchIdxs'
{-@ myIndices :: Alg -> t:ByteStringNE -> BS.ByteString -> MatchIdxsT t @-}
myIndices alg t bs
  | BS.length bs > fringeLen = let right1 = BS.drop (BS.length bs - fringeLen) bs in
                                MatchIdxs t (BS.length bs) left is right1
  | otherwise = Small t bs
  where
    is        = indices alg t bs
    fringeLen = BS.length t - 1
    left      = BS.take fringeLen bs
    -- right1    = BS.drop (BS.length bs - fringeLen) bs

-- ISSUE: get contextual output with --diff
-- ISSUE: why does lazyvar right1 not work? it drops the output type on right1!

{- lazyvar right1 -}

{-@ type OkPos Targ Str = {v:Nat | v <= bLength Str - bLength Targ} @-}
{-@ type ByteStringNE   = {v:BS.ByteString | bLength v > 0 }   @-}
{-@ type ByteStringN N  = {v:BS.ByteString | bLength v == N}   @-}
{-@ type MatchIdxsT T   = {v:MatchIdxs | targ v == T}          @-}

{-@ assume BS.isSuffixOf :: targ:_ -> s:_ -> {v:_ | v => (bLength targ <= bLength s) } @-}
{-@ assume BS.length  :: b:BS.ByteString -> {v:Nat | v == bLength b}  @-}
{-@ assume BS.empty   :: {v:BS.ByteString | bLength v == 0}    @-}
{-@ assume BS.take    :: n:Nat -> b:BS.ByteString -> ByteStringN {min n (bLength b)} @-}
{-@ assume BS.drop    :: n:Nat -> b:{BS.ByteString | n <= bLength b} -> ByteStringN {bLength b - n} @-}
{-@ assume BS.inits   :: b:BS.ByteString -> [{v:BS.ByteString | bLength v <= bLength b}] @-}
{-@ assume BS.append  :: b1:BS.ByteString -> b2:BS.ByteString -> ByteStringN {bLength b1 + bLength b2} @-}
{-@ assume BS.null    :: b:BS.ByteString -> {v:Bool | v <=> (bLength b == 0)} @-}
{-@ assume BS.splitAt :: n:Nat -> b:BS.ByteString -> (ByteStringN {min n (bLength b)}, ByteStringN {max 0 (bLength b - n)}) @-}
{-@ assume BS.head    :: BS.ByteString -> Data.Word.Word8 @-}

{-@ measure target @-}
target :: MatchIdxs -> BS.ByteString
target (Small t _)           = t
target (MatchIdxs t _ _ _ _) = t

{-@ inline min @-}
min :: Int -> Int -> Int
min x y = if x <= y then x else y

{-@ inline max @-}
max :: Int -> Int -> Int
max x y = if x <= y then y else x

-- RJ instance (KnownSymbol t, StringMatch alg) => Monoid (MatchIdxs alg t) where
{-@ mmempty :: t:ByteStringNE -> MatchIdxsT t @-}
mmempty t = Small t BS.empty

{-@ mmconcat :: (Foldable t) => Alg -> tg:ByteStringNE -> t (MatchIdxsT tg) -> (MatchIdxsT tg) @-}
mmconcat alg t = foldr (mmappend alg t) (mmempty t)

{-@ qualif BB(v:Int, n:Int, d:Int, b:BS.ByteString): v <= (n + d) - bLength b @-}

{-@ mmappend :: Alg -> t:ByteStringNE -> MatchIdxsT t -> MatchIdxsT t -> MatchIdxsT t @-}
mmappend alg t mx my =
  let fringeLen = BS.length t - 1
      idxFun    = indices alg t
  in
  case (mx, my) of
    (Small tx x, Small _ y) -> myIndices alg tx (x <> y)
    (Small tx x, MatchIdxs _ yLen ly iy rt) -> MatchIdxs tx xyLen lt is rt
       where
         xyLen = xLen + yLen
         xLen  = BS.length x
         xly   = BS.append x ly
         lt    = BS.take fringeLen xly
         is    = idxFun xly ++ map (+ xLen) iy
    (MatchIdxs tx xLen lt ix rx, Small ty y) -> MatchIdxs tx xyLen lt (ix ++ is) rt
       where
         xyLen = xLen + yLen
         yLen  = BS.length y
         is    = map (+ (xLen - fringeLen)) (idxFun rxy)
         rt    = BS.drop (BS.length rxy - fringeLen) rxy
         rxy   = BS.append rx y
    (MatchIdxs tx xLen lt ix rx, MatchIdxs ty yLen ly iy rt) -> MatchIdxs tx xyLen lt (ix ++ is) rt
       where
         xyLen = xLen + yLen
         is    = ixy ++ map (+ xLen) iy
         ixy   = map (+ (xLen - fringeLen)) $ idxFun (BS.append rx ly)

-- | Example applications
--
-- The bufLen and chunkSz arguments are there to exercise the monoid,
-- though they also foreshadow a parallel implementation.
{-@ indicesBS' :: Alg -> Int -> Int -> ByteStringNE -> BS.ByteString -> [Int] @-}
indicesBS' alg bufLen chunkSz t bs =
  let si = mmconcat alg t . map (mmconcat alg t) . chunksOf bufLen . map (myIndices alg t) $ chunksBS chunkSz bs in
  matchIdxsIs si

{-@ indicesBS, indicesNaive :: Int -> Int -> ByteStringNE -> BS.ByteString -> [Int] @-}
indicesBS    = indicesBS' BM   -- RJ (Proxy :: Proxy BM)
indicesNaive = indicesBS' Spec -- RJ (Proxy :: Proxy Spec)

{-@ isInfixOfBS :: Int -> Int -> ByteStringNE -> BS.ByteString -> Bool @-}
isInfixOfBS bufLen chunkSz t = not . null . indicesBS bufLen chunkSz t

------------------------------------------------------------------------------------------
{-@ invariant {v:BS.ByteString | 0 <= bLength v } @-}
{-@ measure bLength :: BS.ByteString -> Int @-}
{-@ type LNat N = {v:Nat | v < N} @-}

chunksOf :: Int -> [a] -> [[a]]
chunksOf = undefined

{-@ assumeIndices :: t:ByteStringNE -> s:BS.ByteString -> [OkPos t s] @-}
assumeIndices :: BS.ByteString -> BS.ByteString -> [Int]
assumeIndices = undefined
