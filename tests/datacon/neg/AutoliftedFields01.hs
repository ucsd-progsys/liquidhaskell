{-@ LIQUID "--exact-data-cons" @-}

-- data decl in LH and Haskell do not match and the LH one is not a subtype

module AutoliftedFields01 where

{-@ type Nat = { v : Int | v >= 0 } @-}
type Nat = Int

{-@ data T = T { getT :: Float } @-}
data T = T { getT :: Nat }

{-@ f :: { t : T | getT t >= 1 } -> Nat @-}
f :: T -> Nat
f (T x) = x
