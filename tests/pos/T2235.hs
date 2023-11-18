-- | Tests that liquid haskell can deal fine with HasCallStack.
--
-- See https://github.com/ucsd-progsys/liquidhaskell/issues/2235
module T2235 where

import Language.Haskell.Liquid.Prelude (liquidError)
import GHC.Stack

{-@ myhead :: {xs:[a] | len xs > 0} -> a @-}
myhead :: HasCallStack => [a] -> a
myhead (x:_) = x

{-@ type PosInt = {v: Int | v > 0 } @-}
{-@ type List a N = {v : [a] | (len v) = N} @-}
{-@ type Matrix a Rows Cols  = (List (List a Cols) Rows) @-}
{-@ transpose                :: c:Int -> r:PosInt -> Matrix a r c -> Matrix a c r @-}

transpose                    :: Int -> Int -> [[a]] -> [[a]]
transpose 0 _ _              = []
transpose c r ((x:xs) : xss) = (x : map myhead xss) : transpose (c-1) r (xs : map tail xss)
transpose c r ([] : _)       = liquidError "dead code"
transpose c r []             = error "dead code"

