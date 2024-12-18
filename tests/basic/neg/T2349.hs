{-# LANGUAGE GADTs #-}
{-@ LIQUID "--expect-error-containing=is not a subtype of the required type
      VV : {VV##1456 : [GHC.Types.Int] | GHC.Types_LHAssumptions.len VV##1456 == ?b + 1}" @-}
{-@ LIQUID "--reflection" @-}
-- | Test that the refinement types produced for GADTs are
-- compatible with the Haskell types.
module T2349 where

data Expr t where
  I :: Int -> Expr Int

  NIL :: Expr [t]
  CONS :: Int -> Expr t -> Expr [t] -> Expr [t]

{-@
data Expr t where
  I :: Int -> Expr Int
  NIL :: Expr {v:[t] | len v = 0}
  CONS :: i:Nat -> head:Expr t -> tail:Expr {v:[t] | len v = i} ->
          Expr {v:[t] | len v = i+1}
@-}


{-@
bad :: Expr {v:[Int] | len v = 0}
@-}
bad :: Expr [Int]
bad = CONS 0 (I 2) NIL

