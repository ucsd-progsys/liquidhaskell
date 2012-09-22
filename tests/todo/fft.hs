{-# LANGUAGE BangPatterns #-}

module FFT where

import Prelude hiding ((++))
import qualified Data.ByteString.Lazy.Char8      as BS
import qualified Data.ByteString.Lex.Lazy.Double as BS
import qualified Data.Vector as V
import Data.Vector ((!),(++),Vector)
import Data.List hiding ((++))
import Data.Complex
import System.Environment

headerSize bs = (+) 4 (BS.length . BS.concat . Prelude.take 4 . BS.lines $ bs)  
 
dropHeader bs = BS.drop (headerSize bs) $ bs

main = do
   [f] <- getArgs
   s   <- BS.readFile f
   print . V.map (round. realPart) . ifft_CT. fft_CT . parse $ (dropHeader s)

dft :: Vector (Double) -> Vector (Complex Double)
dft xr = V.map (\k -> V.sum (V.imap (arg k) xr)) (numvec n)
 where
   n = V.length xr
   nf = fromIntegral n
   numvec n = V.enumFromStepN 0 1 n
   arg k i x = (x:+0) * exp (-2 * pi * kf * ifl * (0:+1)/nf)
             where
               kf = fromIntegral k
               ifl = fromIntegral i
     
idft :: Vector (Complex Double) -> Vector (Complex Double)
idft xs = V.map (\k ->(/) (V.sum (V.imap (arg k) xs)) nf) (numvec n)
 where
   n = V.length xs
   nf = fromIntegral n
   numvec n = V.enumFromStepN 0 1 n
   arg k i x = x * exp (2 * pi * kf * ifl * (0:+1)/nf)
             where
               kf = fromIntegral k
               ifl = fromIntegral i

fft_CT xs = if V.length xs == 1 then
             dft xs
           else
             let xtop = V.zipWith3 fft_top (fft_CT xse) (fft_CT xso) (V.enumFromStepN 0 1 m)
             
                 xbottom = V.zipWith3 fft_bottom (fft_CT xse) (fft_CT xso) (V.enumFromStepN 0 1 m)
                 xse = V.map (xs !) (V.enumFromStepN 0 2 m)
                 xso = V.map (xs !) (V.enumFromStepN 1 2 m)
                 n = V.length xs
                 nf = fromIntegral n
                 m = n `div` 2
                 fft_top xe xo k = xe + xo * exp (-2 * (0:+1) * pi * k / nf)
                 fft_bottom xe xo k = xe - xo * exp (-2 * (0:+1) * pi * k / nf)
             in              
                 xtop ++ xbottom

ifft_CT xs = if V.length xs == 1 then
              idft xs
           else
              let xtop = V.zipWith3 fft_top (ifft_CT xse) (ifft_CT xso) (V.enumFromStepN 0 1 m)
                  xtop_scaled = V.map (/2) xtop
                  xbottom = V.zipWith3 fft_bottom (ifft_CT xse) (ifft_CT xso) (V.enumFromStepN 0 1 m)
                  xbottom_scaled = V.map (/2) xbottom
                  xse = V.map (xs !) (V.enumFromStepN 0 2 m)
                  xso = V.map (xs !) (V.enumFromStepN 1 2 m)
                  n = V.length xs
                  nf = fromIntegral n
                  m = n `div` 2
                  fft_top xe xo k = xe + xo * exp (2 * (0:+1) * pi * k / nf)
                  fft_bottom xe xo k = xe - xo * exp (2 * (0:+1) * pi * k / nf)
             in              
                xtop_scaled ++ xbottom_scaled


-- Fill a new vector from a file containing a list of numbers.
parse = V.unfoldr step
 where
   step !s = case BS.readDouble s of
     Nothing       -> Nothing
     Just (!k, !t) -> Just (k, BS.tail t)
