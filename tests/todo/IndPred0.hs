module Even where

data Peano where
  Z :: Peano
  S :: Peano -> Peano 

-- AUTO
data EvenProp where 
  Even :: Peano -> EvenProp 

data Even where
  EZ  :: Even
  ESS :: Peano -> Even -> Even

-- AUTO/PRELUDE
{-@ measure prop :: a -> b @-}

{-@ data Even where
      EZ  :: {v:Even | prop v = Even Z}
      ESS :: n:Peano -> {v:Even | prop v = Even n} -> {v:Even | prop v = Even (S (S n)) }
  @-}

{-@ test :: n:Peano -> {v:Even | prop v = Even (S (S n))} -> {v:Even | prop v = Even n} @-}
test :: Peano -> Even -> Even
test n (ESS m q) = q      -- G := p : {prop p  = Even (S (S n)) /\ prop p = Even (S (S m))}
                          --        ; q : {prop q = Even m}
                          --        ==> n = m
                          --        ==> prop q = Even n
