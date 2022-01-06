{-@ LIQUID "--exact-data-cons" @-}

-- data decl in LH is missing but uses a LH-refined type alias correctly

module AutoliftedFields00 where

{-@ type Nat = { v : Int | v >= 0 } @-}
type Nat = Int

data T = T { getT :: Nat }

{-@ f :: { t : T | getT t >= 1 } -> Nat @-}
f :: T -> Nat
f (T x) = x
