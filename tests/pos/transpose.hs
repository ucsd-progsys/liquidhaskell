module Tx (transpose) where

import Language.Haskell.Liquid.Prelude

{-@ type Vec a N    = {v:[a] | (len v) = N} @-}

{-@ type Grid a N M = Vec (Vec a N) M       @-}


{- transpose :: n:Nat
              -> m:{v:Nat | v > 0} 
              -> {v:[{v:[a] | len(v) = n}] | len(v) = m} 
              -> {v:[{v:[a] | len(v) = m}] | len(v) = n} 
  -}

{-@ transpose :: n:Nat -> m:{v:Nat | v > 0}  -> (Grid a n m) -> (Grid a m n) @-}
transpose     :: Int -> Int -> [[a]] -> [[a]]
transpose 0 _ _              = []
transpose n m ((x:xs) : xss) = (x : map head xss) : transpose (n - 1) m (xs : map tail xss)
transpose n m ([] : _)       = liquidError "transpose1" 
transpose n m []             = liquidError "transpose2"

{-@ tx :: n:Nat -> m:{v:Nat | v > 0}  -> (Grid a n m) -> (Grid a m n) @-}

tx                    :: Int -> Int -> [[a]] -> [[a]]
tx 0 _ _              = []
tx n m ((x:xs) : xss) = (x : map head xss) : tx (n - 1) m (xs : map tail xss)
tx n m ([] : _)       = liquidError "tx1" 
tx n m []             = liquidError "tx2"
