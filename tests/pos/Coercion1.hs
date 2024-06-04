{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--no-positivity-check" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-termination" @-}
module Coercion1 where


-- The type variable ‘i’ should be understood as the set of wire indices
data DSL p i t where
  -- Basic operations
  WIRE  :: i -> DSL p i p -- wire (i.e. variable)
  CONST :: p -> DSL p i p -- constant

  SUB :: DSL p i p -> DSL p i p -> DSL p i p -- field substraction
  -- Boolean constructors
  EQL    :: DSL p i p -> DSL p i p -> DSL p i Bool -- equality check
  ISZERO :: DSL p i p -> DSL p i Bool              -- zero check



{-@ measure desugared @-}
desugared :: DSL i p t -> Bool
desugared (EQL {})  = False

desugared (WIRE _)  = True
desugared (CONST _) = True
desugared (SUB p1 p2) = desugared p1 && desugared p2


desugared (ISZERO p)  = desugared p

{-@ desugar :: DSL p i t -> {v:DSL p i t | desugared v} @-}
desugar :: DSL p i t -> DSL p i t
desugar (EQL p1 p2) = ISZERO (SUB (desugar p1) (desugar p2))

desugar (ISZERO p)  = ISZERO (desugar p)

desugar (CONST p) = CONST p
desugar (WIRE i)  = WIRE i
desugar (SUB p1 p2) = SUB (desugar p1) (desugar p2)
