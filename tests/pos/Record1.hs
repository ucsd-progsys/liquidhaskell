module Record1 (trim) where

data Map k a  = Tip

{-@ data Map k a <l :: root:k -> k -> Bool>
         = Tip
  @-}

{-@ measure isBin @-}
isBin :: Map k a -> Bool
isBin Tip = False

trim :: Map k a
trim = undefined 

