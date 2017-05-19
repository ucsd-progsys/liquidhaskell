{-@ LIQUID "--eliminate=all" @-}
-- | This test case is to check that LH properly accounts for the case where GHC Core 
--   contains stuff like:
--   foo :: T 
--   foo = 
--     let t1 = e1 
--         t2 = e2
--         ...
--         tn = en 
--     in
--     let rec bar = e
--     in 
--       bar 
-- 
--  where `T` is a liquid type specification. This sort of stuff is introduced by GHC8 
--  in order to manage the implicit `CallStack` parameters, but it ends up generating 
--  extra KVars where none are needed (as we already have the signature.)

{-@ LIQUID "--no-termination" @-}

module Foo (prop) where

--data Peano a = Z a | S (Peano a) | P (Peano a)
data Peano = Z | S (Peano ) | P (Peano)

{- foo :: Peano -> Nat @-}
foo :: Peano -> Int 
foo = 
  let t0 = 0 
      t1 = 1 
  in
  let baz p = case p of 
                Z  -> t0
                S p -> t1 + baz p 
                P p -> error ms 
              where 
                ms = "yikes"
  in
    baz

-- USE THIS AS THE NEG VERSION
{-@ prop :: Peano -> Nat @-}
prop = foo 
