-- | This test used to produce a subtyping constraint with a kvar in the LHS
--
-- PLE needs to unfold inferType to help the SMT solver, but the information
-- to do the unfolding is in the solution of the kvar. PLE, then, substitutes
-- the kvar with its solution before searching for unfoldings.
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module T2582 where

data Ty = TInt | TBool
data Expr = CONST Int | TRUE | FALSE

{-@ reflect inferType @-}
inferType :: Expr -> Ty
inferType (CONST _) = TInt
inferType TRUE = TBool
inferType FALSE = TBool

{-@ type IntExpr = {e:Expr | inferType e = TInt} @-}

{-@ foo :: IntExpr @-}
foo :: Expr
foo = CONST 42

{-@ bar :: [IntExpr] @-}
bar :: [Expr]
bar = [CONST 42]
