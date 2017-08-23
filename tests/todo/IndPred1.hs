module Even where

data Peano
  = Z
  | S Peano 

data Even where
  EZ  :: Even
  ESS :: Peano -> Even -> Even

-- Move into prelude?
{-@ type Prop E = {v : _ | prop v = E} @-}

{-@ data Even :: Peano -> Prop where
      EZ  :: Prop (Even Z)                                     
      ESS :: n:Nat -> Prop (Even n) -> Prop (Even (S (S n)))   
  @-}

{-@ test :: n:Peano -> {v:Even | prop v = Even (S (S n))} -> {v:Even | prop v = Even n} @-}
test :: Peano -> Even -> Even
test n p@EZ        = p      -- contra "..."
test n p@(ESS m q) = q      -- G := p : {prop p  = Even (S (S n)) /\ prop p = Even (S (S m))}
                            --        ; q : {prop q = Even m}
                            --        ==> n = m
                            --        ==> prop q = Even n
