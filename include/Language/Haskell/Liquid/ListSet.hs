module Language.Haskell.Liquid.ListSet where

{-@ measure listElts :: [a] -> Set_set a 
    listElts([])   = {v | (? Set_emp(v))}
    listElts(x:xs) = {v | v = Set_cup(Set_sng(x), listElts(xs)) }
  @-}
