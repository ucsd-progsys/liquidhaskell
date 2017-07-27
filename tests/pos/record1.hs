module Data.Map.Base (trim) where

data Map k a  = Tip

{-@ data Map k a <l :: root:k -> k -> Bool>
         = Tip
  @-}

{-@ measure isBin :: Map k a -> Bool
    isBin (Tip)          = false
  @-}

trim :: Map k a
trim = undefined 

