module T1531 where

{-@
data IncList a
  = Emp
  | (:<) { hd :: a, tl :: IncList {v:a | hd <= v} }
@-}

data IncList a =
    Emp
  | a :< IncList a

{-@
data IncListt a =
    Empp
  | (:<<) { hdd :: a, tll :: IncListt {v:a | hdd <= v} }
@-}

data IncListt a =
    Empp
  | a :<< IncListt a
