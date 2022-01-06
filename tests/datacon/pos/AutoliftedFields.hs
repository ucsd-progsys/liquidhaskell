{-@ LIQUID "--exact-data-cons" @-}

module AutoliftedFields where

{-@ type Nat = { v : Int | v >= 0 } @-}
type Nat = Int

data T = T { getT :: Nat }

{-@ f :: { t : T | getT t >= 1 } -> Nat @-}
f :: T -> Nat
f (T x) = x
