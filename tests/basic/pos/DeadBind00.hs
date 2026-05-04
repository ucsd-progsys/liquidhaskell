-- | Regression test: dead bindings in where-clauses should be preserved
-- so that LH can analyze them. GHC's simple optimizer normally removes
-- dead bindings via occurrence analysis; our modification to
-- 'addNoInlinePragmasToBinds' marks binder Ids as exported to prevent this.

module DeadBind00 where

{-@ reflect length' @-}
{-@ length' :: xs:[a] -> Nat @-}
length' :: [a] -> Int
length' [] = 0
length' (_:xs) = 1 + length' xs

{-@ f :: xs:[a] -> { length' xs >= 0 } @-}
f :: [a] -> ()
f xs = ()
  where
    zs = length' xs
