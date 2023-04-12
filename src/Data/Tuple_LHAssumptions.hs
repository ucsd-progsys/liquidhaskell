{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.Tuple_LHAssumptions where

import Data.Tuple

{-@
assume Data.Tuple.fst :: {f:(x:(a,b) -> {v:a | v = (fst x)}) | f == fst }
assume Data.Tuple.snd :: {f:(x:(a,b) -> {v:b | v = (snd x)}) | f == snd }

measure fst :: (a, b) -> a
  fst (a, b) = a

measure snd :: (a, b) -> b
  snd (a, b) = b

qualif Fst(__v:a, __y:b): (__v = (fst __y))
qualif Snd(__v:a, __y:b): (__v = (snd __y))
@-}
