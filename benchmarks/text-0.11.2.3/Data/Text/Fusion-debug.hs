{-# LANGUAGE BangPatterns, MagicHash #-}

module Data.Text.Fusion ( outerL ) where

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

--LIQUID
import GHC.ST (ST, runST)
import Language.Haskell.Liquid.Prelude

default (Int)

fst :: (a, b) -> a
fst = undefined

snd :: (a, b) -> b
snd = undefined

{-@ Lazy mapAccumL @-}
mapAccumL :: (a -> Char -> (a, Char)) -> a -> Stream Char -> (a, Text)
mapAccumL f z0 (Stream next0 s0 len) = (nz, I.textP na 0 nl)
  where
    mlen  = upperBound 4 len
    -- na    = fst blob
    -- nz    = fst (snd blob)
    -- nl    = snd (snd blob)
    (na, (nz,nl))
    -- blob
        = runST
                      -- (blob f next0 mlen z0 s0)
                       ( do arrBLOB0  <- A.new mlen
                            (marr, x) <- outerL f next0 arrBLOB0 mlen z0 s0 0
                            arr       <- A.unsafeFreeze marr
                            return (arr, x) )


{- outerL :: (b -> c -> (b, Char))
           -> (t -> Step t c)
           -> A.MArray s
           -> Int
           -> b
           -> t
           -> Int
           -> ST s (A.MArray s, (b, Int)) -}

outerL :: (b -> t1 -> (b, Char))
           -> (t -> Step t t1)
           -> A.MArray s
           -> Int
           -> b
           -> t
           -> Int
           -> ST s (A.MArray s, (b, Int))
outerL f next0 arr top = loop
  where
    loop !z !s !i =
            case next0 s of
              Done          -> return (arr, (z, i))
              Skip s'       -> loop z s' i
              Yield x s'
                | j >= top  -> {-# SCC "mapAccumL/resize" #-} do
                               let top' = (top + 1) * 2 -- LIQUID `shiftL` 1
                               arr' <- A.new top'
                               A.copyM arr' 0 arr 0 top
                               outerL f next0 arr' top' z s i
                | otherwise -> do d <- unsafeWrite arr i c
                                  loop z' s' (i+d)
                where (z',c) = f z x
                      j | ord c < 0x10000 = i
                        | otherwise       = i + 1
