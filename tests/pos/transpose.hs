module Tx (transpose) where

import Language.Haskell.Liquid.Prelude

{-@ assert transpose :: n:Nat
                     -> m:{v:Nat | v > 0} 
                     -> {v:[{v:[a] | len(v) = n}] | len(v) = m} 
                     -> {v:[{v:[a] | len(v) = m}] | len(v) = n} 
  @-}

transpose :: Int -> Int -> [[a]] -> [[a]]
transpose 0 _ _              = []
transpose n m ((x:xs) : xss) = (x : map head xss) : transpose (n - 1) m (xs : map tail xss)
transpose n m ([] : _)       = liquidError "transpose1" 
transpose n m []             = liquidError "transpose2"


{-@ assert tx :: n:Nat
              -> m:{v:Nat | v > 0} 
              -> {v:[{v:[a] | len(v) = n}] | len(v) = m} 
              -> {v:[{v:[a] | len(v) = m}] | len(v) = n} 
  @-}

{-@ type Grid a N M = {v:[{v:[a] | len(v) = n}] | len(v) = m}  @-}

tx                    :: Int -> Int -> [[a]] -> [[a]]
tx 0 _ _              = []
tx n m ((x:xs) : xss) = (x : map head xss) : tx (n - 1) m (xs : map tail xss)
tx n m ([] : _)       = liquidError "tx1" 
tx n m []             = liquidError "tx2"
