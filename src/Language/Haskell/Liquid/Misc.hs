{-# LANGUAGE CPP                       #-}
{-# LANGUAGE TupleSections             #-}

module Language.Haskell.Liquid.Misc where

import Control.Applicative
import System.FilePath

import qualified Data.List as L

import Language.Fixpoint.Misc (errorstar)

import Data.List              (sort)

import Paths_liquidhaskell

firstDuplicate :: Ord a => [a] -> Maybe a
firstDuplicate = go . sort
  where
    go (y:x:xs) | x == y    = Just x 
                | otherwise = go (x:xs)
    go _                    = Nothing            


safeIndex err n ls 
  | n >= length ls
  = errorstar err
  | otherwise 
  = ls !! n

(!?) :: [a] -> Int -> Maybe a
[]     !? _ = Nothing
(x:_)  !? 0 = Just x
(_:xs) !? n = xs !? (n-1)

safeFromJust _  (Just x) = x
safeFromJust err _        = errorstar err

fst4 (a,_,_,_) = a
snd4 (_,b,_,_) = b

mapFourth4 f (x, y, z, w) = (x, y, z, f w)

addFst3   a (b, c) = (a, b, c)
addThd3   c (a, b) = (a, b, c)
dropFst3 (_, x, y) = (x, y)
dropThd3 (x, y, _) = (x, y)

replaceN n y ls = [if i == n then y else x | (x, i) <- zip ls [0..]]

fourth4 (_,_,_,x) = x
third4  (_,_,x,_) = x

mapSndM f (x, y) = return . (x,) =<< f y

firstM  f (a,b) = (,b) <$> f a
secondM f (a,b) = (a,) <$> f b

first3M  f (a,b,c) = (,b,c) <$> f a
second3M f (a,b,c) = (a,,c) <$> f b
third3M  f (a,b,c) = (a,b,) <$> f c

third3 f (a,b,c) = (a,b,f c)

zip4 (x1:xs1) (x2:xs2) (x3:xs3) (x4:xs4) = (x1, x2, x3, x4) : (zip4 xs1 xs2 xs3 xs4) 
zip4 _ _ _ _                             = []

#if __GLASGOW_HASKELL__ < 710
ghc = "ghc-7.8"
#else
ghc = "ghc-7.10"
#endif

getIncludeDir      = dropFileName <$> getDataFileName ("include" </> "Prelude.spec")
getCssPath         = getDataFileName $ "syntax" </> "liquid.css"
getCoreToLogicPath = fmap (</> "CoreToLogic.lg") getIncludeDir


maximumWithDefault zero [] = zero
maximumWithDefault _    xs = maximum xs

{-@ type ListN a N = {v:[a] | len v = N} @-}
{-@ type ListL a L = ListN a (len L) @-}

{-@ safeZipWithError :: _ -> xs:[a] -> ListL b xs -> ListL (a,b) xs / [xs] @-}
safeZipWithError msg (x:xs) (y:ys) = (x,y) : safeZipWithError msg xs ys
safeZipWithError _   []     []     = []
safeZipWithError msg _      _      = errorstar msg

safeZip3WithError msg (x:xs) (y:ys) (z:zs) = (x,y,z) : safeZip3WithError msg xs ys zs
safeZip3WithError _   []     []     []     = []
safeZip3WithError msg _      _      _      = errorstar msg

mapNs ns f xs = foldl (\xs n -> mapN n f xs) xs ns

mapN 0 f (x:xs) = f x : xs
mapN n f (x:xs) = x : mapN (n-1) f xs
mapN _ _ []     = []


 
pad _ f [] ys   = (f <$> ys, ys)
pad _ f xs []   = (xs, f <$> xs)
pad msg _ xs ys
  | nxs == nys  = (xs, ys)
  | otherwise   = errorstar $ "pad: " ++ msg
  where
    nxs         = length xs
    nys         = length ys



ordNub :: Ord a => [a] -> [a]
ordNub = map head . L.group . L.sort

intToString :: Int -> String
intToString 1 = "1st"
intToString 2 = "2nd"
intToString 3 = "3rd"
intToString n = show n ++ "th"

