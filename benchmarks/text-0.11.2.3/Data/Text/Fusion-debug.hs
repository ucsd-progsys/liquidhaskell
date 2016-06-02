{-# LANGUAGE BangPatterns, MagicHash #-}

-- FAST
module Data.Text.Fusion (mapAccumL) where

-- SLOW module Data.Text.Fusion where

import Prelude (Bool(..), Char, Maybe(..), Monad(..), Int,
                Num(..), Ord(..), ($), (&&),
                fromIntegral, otherwise, undefined)
import Data.Bits ((.&.))
import Data.Text.Internal (Text(..))
import Data.Text.Private (runText)
import Data.Text.UnsafeChar (ord, unsafeChr, unsafeWrite)
import Data.Text.UnsafeShift (shiftL, shiftR)
import qualified Data.Text.Array as A
import qualified Data.Text.Fusion.Common as S
import Data.Text.Fusion.Internal
import Data.Text.Fusion.Size
import qualified Data.Text.Internal as I
import qualified Data.Text.Encoding.Utf16 as U16

import GHC.ST (ST, runST)
import Language.Haskell.Liquid.Prelude

default (Int)

{-@ fst :: (a, b) -> a @-}
fst :: (a, b) -> a
fst = undefined

{-@ snd :: (a, b) -> b @-}
snd :: (a, b) -> b
snd = undefined

mapAccumL :: (a -> Char -> (a, Char)) -> a -> Stream Char -> (a, Text)
mapAccumL f z0 (Stream next0 s0 len) = (nz, I.textP na 0 nl)
  where
    mlen  = upperBound 4 len
    na    = fst blob
    nz    = fst (snd blob)
    nl    = snd (snd blob)
    -- (na, (nz, nl))
    blob
        = runST
                       ( do arrBLOB0  <- A.new mlen
                            (marr, x) <- outerL f next0 arrBLOB0 mlen z0 s0 0
                            arr       <- A.unsafeFreeze marr
                            return (arr, x) )

-- SLOW
{-@
  outerL :: (b -> t1 -> (b, Char))
            -> (t -> Step t t1)
            -> A.MArray s
            -> Int
            -> b
            -> t
            -> Int
            -> ST s (A.MArray s, (b, Int))
  @-}

-- FAST
outerL :: (b -> t1 -> (b, Char))
           -> (t -> Step t t1)
           -> A.MArray s
           -> Int
           -> b
           -> t
           -> Int
           -> ST s (A.MArray s, (b, Int))

outerL = undefined
