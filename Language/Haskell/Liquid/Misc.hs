{-# LANGUAGE TupleSections             #-}

module Language.Haskell.Liquid.Misc where

import Language.Fixpoint.Misc (errorstar)

safeIndex err n ls 
  | n >= length ls
  = errorstar err
  | otherwise 
  = ls !! n

safeFromJust err (Just x) = x
safeFromJust err _        = errorstar err

dropFst3 (_, x, y) = (x, y)

replaceN n y ls = [if i == n then y else x | (x, i) <- zip ls [0..]]

mapSndM f (x, y) = return . (x,) =<< f y

