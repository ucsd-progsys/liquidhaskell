-- | Demonstrates ghost expression variables (@REx@) arising from
-- A-normalisation of complex predicate arguments in abstract-refinement types.
--
-- When LiquidHaskell checks this module, the @addCGEnv@ case for @REx@ fires
-- for each call site where the return type contains an abstract refinement
-- applied to a complex expression (such as @i+1@).  The console output
-- (when instrumented) looks like:
--
-- @
-- addCGEnv REx: x=lq_anf$...
--   t=exists [ex#0:{v : GHC.Internal.Types.Int | v == i + 1}].
--             {v : a | papp2 ... v ex#0}
-- @
--
-- The ghost variable @ex#0@ names the value @i+1@ so that the fixpoint
-- solver can refer to it without duplicating the expression.

{-@ LIQUID "--no-termination" @-}

module TestREx () where

-- A step function whose return type mentions the abstract refinement at
-- a *complex* argument position (@i+1@).  When LH A-normalises a call
-- @next i x@, it introduces a ghost variable @ex#0@ with type
-- @{v:Int | v == i+1}@ and wraps the result type with @REx ex#0 ...@,
-- which triggers the @addCGEnv REx@ case.
{-@ assume next :: forall a <p :: Int -> a -> Bool>.
                   i:Int -> a<p i> -> a<p (i + 1)> @-}
next :: Int -> a -> a
next _ x = x

-- Two steps: calls @next@ twice, each producing an @REx@-wrapped type.
-- Console output will show two @addCGEnv REx@ lines during verification.
{-@ twoSteps :: forall a <p :: Int -> a -> Bool>.
                i:Int -> a<p i> -> a<p (i + 2)> @-}
twoSteps :: Int -> a -> a
twoSteps i x = next (i + 1) (next i x)
