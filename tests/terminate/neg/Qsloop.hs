{-@ LIQUID "--expect-any-error" @-}
module Qsloop where

quickSort []       = []
quickSort xs@(x:_) = lts ++  gts 
  where 
    lts          = quickSort [y | y <- xs, y < x]
    gts          = quickSort [z | z <- xs, z >= x]


