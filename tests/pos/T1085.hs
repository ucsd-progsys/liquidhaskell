{-@ LIQUID "--exact-data-cons"   @-}

module T1085 where

{-@ data HEither a b = HLeft a | HRight b @-}
data HEither a b = HLeft a | HRight b

{-@ data HMaybe a = HJust a | HNothing @-}
data HMaybe a = HJust a | HNothing
