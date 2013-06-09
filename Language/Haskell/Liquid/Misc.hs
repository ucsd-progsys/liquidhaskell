module Language.Haskell.Liquid.Misc where

import Language.Fixpoint.Misc (errorstar)

safeFromJust err (Just x) = x
safeFromJust err _        = errorstar err

safeZip3 err [] [] []             
  = []
safeZip3 err (x:xs) (y:ys) (z:zs) 
  = (x, y, z) : (safeZip3 err xs ys zs)
safeZip3 err _ _ _
  = errorstar $ "safeZip3: " ++ err 

dropFst3 (_, x, y) = (x, y)

mapN n f ls = [if i == n then f x else x | (x, i) <- zip ls [0..]]
