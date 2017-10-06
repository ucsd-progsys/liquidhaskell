{-@ LIQUID "--exact-data-cons"   @-}

{-@ data HEither a b = HLeft a | HRight b @-}
data HEither a b = HLeft a | HRight b

{-@ data HMaybe a = HJust a | HNothing @-}
data HMaybe a = HJust a | HNothing
