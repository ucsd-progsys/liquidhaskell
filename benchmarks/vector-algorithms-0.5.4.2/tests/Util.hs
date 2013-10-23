{-# LANGUAGE TypeOperators #-}

module Util where

import Control.Monad
import Control.Monad.ST

import Data.Word
import Data.Int

import qualified Data.ByteString as B

import qualified Data.Vector as V

import Data.Vector.Mutable hiding (length)

import Test.QuickCheck


mfromList :: [e] -> ST s (MVector s e)
mfromList l = do v <- new (length l)
                 fill l 0 v
 where
 fill []     _ v = return v
 fill (x:xs) i v = do write v i x
                      fill xs (i+1) v

instance (Arbitrary e) => Arbitrary (V.Vector e) where
  arbitrary = fmap V.fromList arbitrary

instance Arbitrary B.ByteString where
  arbitrary = B.pack `fmap` arbitrary

