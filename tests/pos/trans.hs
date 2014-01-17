module Tx () where

import Language.Haskell.Liquid.Prelude

{- THIS IS A RANDOM COMMENT -}

{-@ foo :: x: Int -> Int @-}
foo :: Int -> Int
foo x = x + 1

{-@ transpose :: n:Int
              -> m:{v:Int | v > 0} 
              -> {v:[{v:[a] | len(v) = n}] | len(v) = m} 
              -> {v:[{v:[a] | len(v) = m}] | len(v) = n} 
  @-}
transpose :: Int -> Int -> [[a]] -> [[a]]
transpose 0 _ _              = []
transpose n m ((x:xs) : xss) = (x : map head xss) : transpose (n - 1) m (xs : map tail xss)
transpose n m ([] : _)       = liquidError "transpose1" 
transpose n m []             = liquidError "transpose2"

-- NEEDS TAGS: map head xss = [ h | (h:_) <- xss]
-- NEEDS TAGS: map tail xss = [t | (_:t) <- xss]


