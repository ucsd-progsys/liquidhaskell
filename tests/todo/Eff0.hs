-- | Trivial test for effects

module Eff0 (test0) where

import EffSTT

{-@ type IntN N = {v:Int | v = N} @-}

{-@ test0 :: STT (IntN {10}) @-}
test0 :: STT Int
test0 =
  newPtr 0       `bind` \p  ->
  writePtr p 10  `bind` \_  ->
  readPtr p      `bind` \v1 ->
  return v1
