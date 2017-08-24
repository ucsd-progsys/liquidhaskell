module Even where

data Peano
  = Z
  | S Peano

data Even where
  EZ  :: Even
  ESS :: Peano -> Even -> Even

{-@ data Even :: Peano -> Prop where
      EZ  :: {v:Even | prop v = Even Z}
      ESS :: n:Peano -> {v:Even | prop v = Even n} -> {v:Even | prop v = Even (S (S n)) }
  @-}

{-

data Member a :: a -> [a] -> Prop where
  Here  :: x:a -> ys:[a] -> Prop (Member x (x:ys))
  There :: x:a -> y:a -> ys:[a] -> Prop (Member x ys) -> Prop (Member x (y:ys))

Inductive prefix_spec : list A -> list A -> Prop :=
    | prefix_nil  : forall (l: list A),
        prefix_spec nil l
    | prefix_cons : forall (a: A) (l m:list A),
        prefix_spec l m -> prefix_spec (a::l) (a::m).
  
0. Refactor `DataDecl`

    - allow for OUTPUT type
    - allow for GADT syntax

1. DataProp
    - just like DataDecl (?) but with OUTPUT TYPE
    - parser
    - spec

2. DataProp -> DataDecl
    - Create the

ctors

  EZ  :: {v:Even | prop v = Even Z}
  ESS :: n:Peano -> {v:Even | prop v = Even n} -> {v:Even | prop v = Even (S (S n)) }

datatypes

  datatype Even#Prop = [
    | Even { x0 : Peano }
  ]

  datatype Even = [
    | EZ  { }
    | ESS { x0 : Peano, x1 : Even }
  ]

 -}


{-@ test :: n:Peano -> {v:Even | prop v = Even (S (S n))} -> {v:Even | prop v = Even n} @-}
test :: Peano -> Even -> Even
test n p@EZ        = p      -- contra "..."
test n p@(ESS m q) = q      -- G := p : {prop p  = Even (S (S n)) /\ prop p = Even (S (S m))}
                            --        ; q : {prop q = Even m}
                            --        ==> n = m
                            --        ==> prop q = Even n
