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

{-@ LIQUID "--no-termination" @-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{- LANGUAGE KindSignatures -}
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

traceMsg msg x = trace (msg ++ show x) x

chunksBS :: Int -> BS.ByteString -> [BS.ByteString]
chunksBS n' xs | BS.null xs = []
               | otherwise = x : chunksBS n xs'
    where (x,xs') = BS.splitAt n xs
          n = max 1 n'


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
indicesSpec :: BS.ByteString -> BS.ByteString -> [Int]
indicesSpec targ = map ((BS.length targ -) . BS.length) . filter (targ `BS.isSuffixOf`) . BS.inits


-- | Datatype to name string matching algorithms; will use it's lifted
-- version put choice in type.
data Alg = BM  -- ^ Boyer-Moore from stringsearch package
         | Spec  -- ^ Naive spec

indices :: Alg -> BS.ByteString -> BS.ByteString -> [Int]
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
              , bs      :: {bs:BS.ByteString | bLength bs < bLength targ}
              }

      | MatchIdxs
              { targ    :: ByteStringNE
              , input   :: {input : Int | input >= bLength targ}
              , left    :: {left  : BS.ByteString | bLength left == bLength targ - 1}
              , matches :: [{v:Int | v <= input - bLength targ}]
              , right   :: {right: BS.ByteString | bLength right == bLength right - 1}
              }
  @-}


matchIdxsIs :: MatchIdxs -> [Int]
matchIdxsIs (Small _ _) = []
matchIdxsIs (MatchIdxs _ _ _ is _) = is

-- | create a 'MatchIdxs'
{-@ myIndices :: Alg -> ByteStringNE -> BS.ByteString -> MatchIdxs @-}
myIndices alg t bs
  | BS.length bs > fringeLen = MatchIdxs t (BS.length bs) left is right
  | otherwise = Small t bs
  where
    is        = indices alg t bs
    fringeLen = BS.length t - 1
    left      = BS.take fringeLen bs
    right     = BS.drop (BS.length bs - fringeLen) bs

{-@ type NatEq N = {v:Nat | v == N} @-}
{-@ type ByteStringNE  = {v:BS.ByteString | bLength v > 0 }   @-}
{-@ type ByteStringN N = {v:BS.ByteString | bLength v == N}   @-}
{-@ assume BS.length :: b:BS.ByteString -> NatEq (bLength b)  @-}
{-@ assume BS.empty  :: {v:BS.ByteString | bLength v == 0}    @-}
{-@ assume BS.take   :: n:Nat -> b:BS.ByteString -> ByteStringN {min n (bLength b)} @-}

{-@ inline min @-}
min :: Int -> Int -> Int
min x y = if x <= y then x else y

-- RJ instance (KnownSymbol t, StringMatch alg) => Monoid (MatchIdxs alg t) where
{-@ mmempty :: ByteStringNE -> MatchIdxs @-}
mmempty t = Small t BS.empty -- mempty

mmconcat :: Alg -> BS.ByteString -> [MatchIdxs] -> MatchIdxs
mmconcat alg t mxs = undefined

{-@ mmappend :: Alg -> ByteStringNE -> MatchIdxs -> MatchIdxs -> MatchIdxs @-}
-- mmappend :: Alg -> BS.ByteString -> MatchIdxs -> MatchIdxs -> MatchIdxs
mmappend alg t mx my = case (mx, my) of
  (Small tx x, Small _ y) -> myIndices alg tx (x <> y)
  (Small tx x, MatchIdxs _ yLen ly iy rt) -> MatchIdxs tx (xLen + yLen) lt is rt
     where
       xLen = BS.length x
       xly  = x <> ly
       lt   =  BS.take fringeLen xly
       is   = idxFun xly <> map (+ xLen) iy
  (MatchIdxs tx xLen lt ix rx, _) -> MatchIdxs tx (xLen + yLen) lt (ix <> is) rt
          where (yLen, is, rt) = case my of
                  Small ty y -> (BS.length y, is, rt) where
                    rxy = rx <> y
                    rt = BS.drop (BS.length rxy - fringeLen) rxy
                    is = map (+ (xLen - fringeLen)) (idxFun rxy)
                  MatchIdxs ty yLen ly iy rt -> (yLen, is, rt) where
                    is = ixy <> map (+ xLen) iy
                    ixy = map (+ (xLen - fringeLen)) $ idxFun (rx <> ly)
      where
        fringeLen = BS.length t - 1
        idxFun    = indices alg t



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
isInfixOfBS bufLen chunkSz targ = not . null . indicesBS bufLen chunkSz targ


------------------------------------------------------------------------------------------
{-@ measure bLength :: BS.ByteString -> Int @-}

chunksOf :: Int -> [a] -> [[a]]
chunksOf = undefined

{-@ assumeIndices :: targ:BS.ByteString -> str:BS.ByteString -> [{v:Nat | v < bLength str}] @-}
assumeIndices :: BS.ByteString -> BS.ByteString -> [Int]
assumeIndices = undefined
