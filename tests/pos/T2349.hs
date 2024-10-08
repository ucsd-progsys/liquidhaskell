{-# LANGUAGE GADTs #-}
{-@ LIQUID "--reflection" @-}
module TestModule where

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