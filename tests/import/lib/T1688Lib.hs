{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}

module T1688Lib where

type Vname = Int

{-@ measure propOf :: a -> b @-}
{-@ type ProofOf E = { proofObj:_ | propOf proofObj = E } @-}

data Expr = Bc Bool                   -- True, False
          | Ic Int                    -- 0, 1, 2, ...
          | Lambda Int Expr         -- \x.e          abstractions
          | App Expr Expr             -- e e'          applications

data Basic = TBool         -- Bool
           | TInt          -- Int

data StepProp where
    Step :: Expr -> Expr -> StepProp

data StepProof where
    EFake :: Vname -> Expr -> Expr -> StepProof

{-@ data StepProof where
      EFake :: x:Vname -> e:Expr -> v:_ -> ProofOf( Step (App (Lambda x e) v) e)
  @-}
