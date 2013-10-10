{-@ LIQUID "--no-termination" @-}

module Tx (transpose) where

import Language.Haskell.Liquid.Prelude

{-@ type Vec a N    = {v:[a] | (len v) = N}       @-}

{-@ type Grid a Cols Rows = Vec (Vec a Cols) Rows @-}

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

-- | Transposing a matrix

{-@ type Mat a = {m0:[{v:[a] | (len v) = (cols m0)}] | true } @-}

{-@ type MatC a C = {m0:[{v:[a] | ((len v) = (cols m0) && (len v) = (len C))}] | true } @-}

{-@ tx :: m:{v:(Mat a) | ((len v) > 0)} -> {v:(MatC a m) | (len v) = (cols m)} @-}
tx :: [[a]] -> [[a]]
tx ([]:_)       = []
tx ((x:xs) : xss) = fstRow : restRows' 
                    where fstRow     = x : map head xss
                          restRows'  = tx restRows
                          restRows   = xs : map tail xss
tx []             = liquidError "tx"

-- DEBUG
{-@ eqLen :: xs:[a] -> yss:[{v:[b] | (len v) = (len xs)}] -> [[b]] @-}
eqLen xs yss = map (\ys -> liquidAssert (length xs == length ys) ys) yss

-- | Specifications 

{-@ measure cols :: [[a]] -> Int
    cols ([])   = 0
    cols (x:xs) = (len x)
  @-}

{-@ measure rows :: [[a]] -> Int
    rows ([])   = 0
    rows (x:xs) = 1 + (rows xs)
  @-}

{-@ type Mat a = {m0:[{v:[a] | (len v) = (cols m0)}] | true } @-}

{-@ predicate Dim V R C = (((len V) = R) && ((cols V) = C)) @-}

-- {- mat_2_3 :: {v: (Mat Int) | (Dim v 2 3)} -}
-- mat_2_3 :: [[Int]]
-- mat_2_3 
--   = [ [1,2,3]
--     , [4,5,6] ]
--           
-- {- mat :: (Mat Int) -}
-- mat :: [[Int]]
-- mat 
--   = [ [1,2]
--     , [7,7]
--     , [5,6]
--     , [7,8] ]


