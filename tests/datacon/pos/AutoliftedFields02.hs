{-@ LIQUID "--exact-data-cons" @-}

-- data decl in LH and Haskell do not match but the LH is a subtype

module AutoliftedFields02 where

{-@ type Nat = { v : Int | v >= 0 } @-}
type Nat = Int

{-@ data T = T { getT :: Nat } @-}
data T = T { getT :: Int }

{-@ f :: { t : T | getT t >= 0 } -> Nat @-}
f :: T -> Nat
f (T x) = x
