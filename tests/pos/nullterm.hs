{-@ LIQUID "--no-termination" @-}

module NullTerm () where

import Language.Haskell.Liquid.Prelude
import LiquidArray

upperCaseString' :: Int -> Int -> (Int -> Int) -> (Int -> Int)
upperCaseString' n i s =
  let c = get i s in
  if c == 0 then s
            else upperCaseString' n (i + 1) (set i (c + 32) s)

{-@ upperCaseString ::
      n: {v: Int | v > 0} ->
      s: (j: {v : Int | (0 <= v && v < n)} ->
          {v: Int | (j = n - 1 => v = 0)}) ->
      (j: {v : Int | (0 <= v && v < n)} ->
       {v: Int | (j = n - 1 => v = 0)})
@-}
upperCaseString :: Int -> (Int -> Int) -> (Int -> Int)
upperCaseString n s = upperCaseString' n 0 s
