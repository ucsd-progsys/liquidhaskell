-- | Regression test for https://github.com/ucsd-progsys/liquidhaskell/issues/2536
-- Dependent pair types should be usable across function call boundaries.
module T2536 where

data T = T Int

{-@ lemma :: [(i::Int, {t:T| t = T i})] -> () @-}
lemma :: [(Int, T)] -> ()
lemma _ = ()

{-@ g :: i:Int -> [(i::Int, {t:T| t = T i})] @-}
g :: Int -> [(Int, T)]
g i = [(i, T i)]

f :: Int -> ()
f i = lemma (g i)
