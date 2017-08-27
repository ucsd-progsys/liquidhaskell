module Even where

data Peano
  = Z
  | S Peano

{- AUTOMATICALLY GENERATE

   data EvProp where
     Ev :: Peano -> EvProp

   data EvProp 0 = [
      Ev { x0: Peano }
   ]

 -}

data Ev where
  EZ  :: Ev
  ESS :: Peano -> Ev -> Ev

{-@ data Ev :: Peano -> Prop where
      EZ  :: Prop (Ev Z)
    | ESS :: n:Peano -> Prop (Ev n) -> Prop (Ev (S (S n)))
  @-}

{-@ test :: n:Peano -> Prop (Ev (S (S n))) -> Prop (Ev n) @-}
test :: Peano -> Ev -> Ev
test n (ESS m q) = q












--------------------------------------------------------------------------------
-- PRELUDE
--------------------------------------------------------------------------------
{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}
--------------------------------------------------------------------------------
