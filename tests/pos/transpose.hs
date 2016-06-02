{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Tx (transpose, transpose', transpose'') where

import Language.Haskell.Liquid.Prelude

-- | Specifying a matrix

{-@ type Matrix a       = {m0:[{v:[a] | (len v) = (cols m0)}] | true } @-}

{-@ type MatrixCR a C R = {m0:[{v:[a] | (len v) = C}] | (((len m0) = R) && (R > 0 => (cols m0) = C)) } @-}

{-@ measure cols :: [[a]] -> Int
    cols ([])   = 0
    cols (x:xs) = (len x)
  @-}

-- | A Few Simple Examples (which run VERY slowly)

{-@ predicate Dim V C R = (((len V) = R) && ((cols V) = C)) @-}

{-@ mat_3_2 :: {v: Matrix Int | (Dim v 3 2)} @-}
mat_3_2 :: [[Int]]
mat_3_2 = [ [1,2,3]
          , [4,5,6] ]
          
{-@ mat_2_4 :: {v: Matrix Int | (Dim v 2 4)} @-}
mat_2_4 :: [[Int]]
mat_2_4 = [ [1,2]
          , [3,4]
          , [5,6]
          , [7,8] ]

-- | Old fashioned transpose with explicit dimensions

{- transpose :: c:Nat
             -> r:{v:Nat | v > 0} 
             -> {v:[{v:[a] | (len v) = c}] | (len v) = r} 
             -> {v:[{v:[a] | (len v) = r}] | (len v) = c} 
  -}

{-@ transpose :: c:Nat -> r:{v:Nat | v > 0}  -> (MatrixCR a c r) -> (MatrixCR a r c) @-}
transpose     :: Int -> Int -> [[a]] -> [[a]]
transpose 0 _ _              = []
transpose n m ((x:xs) : xss) = (x : map head xss) : transpose (n - 1) m (xs : map tail xss)
transpose n m ([] : _)       = liquidError "transpose1" 
transpose n m []             = liquidError "transpose2"


{-@ transpose' :: m:{v:(Matrix a) | ((len v) > 0)} -> (MatrixCR a (len m) (cols m)) @-}
transpose' :: [[a]] -> [[a]]
transpose' ([]:_)         = []
transpose' ((x:xs) : xss) = (x : map head xss) : transpose' (xs : map tail xss)
transpose' []             = liquidError "transpose'"

-- | A wrapper implementing the explicit transpose using the implicit one

{-@ transpose''     :: c:Nat -> r:{v:Nat | v > 0}  -> (MatrixCR a c r) -> (MatrixCR a r c) @-}
transpose''         :: Int -> Int -> [[a]] -> [[a]]
transpose'' n m xss = transpose' xss

