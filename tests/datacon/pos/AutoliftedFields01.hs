{-@ LIQUID "--exact-data-cons" @-}

-- data decl in LH and Haskell give different names to the fields, but use them
-- in valid ways.

module AutoliftedFields01 where

{-@ type Nat = { v : Int | v >= 0 } @-}
type Nat = Int

{-@ data T = T { getMyT :: Nat } @-}
data T = T { getT :: Nat }

{-@ f :: { t : T | getT t == getMyT t } -> Nat @-}
f :: T -> Nat
f (T x) = x
