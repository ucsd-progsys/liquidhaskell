{-# LANGUAGE TupleSections             #-}

module Language.Haskell.Liquid.Misc where

import Control.Applicative

import Language.Fixpoint.Misc (errorstar)

safeIndex err n ls 
  | n >= length ls
  = errorstar err
  | otherwise 
  = ls !! n

safeFromJust err (Just x) = x
safeFromJust err _        = errorstar err

addFst3   a (b, c) = (a, b, c)
dropFst3 (_, x, y) = (x, y)

replaceN n y ls = [if i == n then y else x | (x, i) <- zip ls [0..]]

mapSndM f (x, y) = return . (x,) =<< f y

firstM  f (a,b) = (,b) <$> f a
secondM f (a,b) = (a,) <$> f b

first3M  f (a,b,c) = (,b,c) <$> f a
second3M f (a,b,c) = (a,,c) <$> f b
third3M  f (a,b,c) = (a,b,) <$> f c

zip4 (x1:xs1) (x2:xs2) (x3:xs3) (x4:xs4) = (x1, x2, x3, x4) : (zip4 xs1 xs2 xs3 xs4) 
zip4 _ _ _ _                             = []

