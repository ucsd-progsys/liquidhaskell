{-# LANGUAGE GADTs #-}
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
  CONS :: xxxxx:_ -> head:Expr t -> tail:Expr {v:[t] | len v = xxxxx} ->
          Expr {v:[t] | len v = xxxxx+1}
@-}