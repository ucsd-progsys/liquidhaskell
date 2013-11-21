module BareCrash where

{-@ measure isReal :: Space -> Prop
    isReal (Null)       = false
    isReal (Rreal pv n) = true
 @-}


data Space = Null | Real Int Int 
  deriving (Show, Eq)
