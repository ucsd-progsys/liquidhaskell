module Isort () where

data F = F 

{-@ measure lenF @-}
lenF :: F -> Int
lenF F = 0


{- some interaction needed to check the def of lenF satisfies the invariant! -}

{-@ using (F) as  {v: F | (lenF v > 0)} @-}

{-

Mt has type 

  {v:F | lenF v == 0  }  -- from measure 
  {v:F | lenF v > 0}  -- from invariant

which is inconsistent !
-}

{-@ insert :: F -> {v: F |  false }  @-}
insert :: F -> F
insert F = F

