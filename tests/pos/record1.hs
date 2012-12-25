module Data.Map.Base (trim) where

data Map k a  = Tip

{-@ data Map k a <l :: root:k -> k -> Prop>
         = Tip
  @-}

{-@ measure isBin :: Map k a -> Prop
    isBin (Tip)          = false
  @-}

trim :: Map k a
trim = error "TODO"

