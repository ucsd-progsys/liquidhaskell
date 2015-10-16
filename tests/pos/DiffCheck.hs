{- Test diffcheck. Has been rigged to not test badFn which has not "changed",
  but should test goodFn, which has "changed", and should see that goodDep
  has not "changed". Should return safe, despite badFn being unsafe -}

{-@ LIQUID "--diffcheck" @-}

module DiffCheck where

{-@ type Zero = {v:Int | v == 0} @-}
{-@ type One = {v:Int | v == 1} @-}
{-@ type Two = {v:Int | v == 2} @-}

{-@ badFn :: Zero -> Bool @-}
badFn :: Int -> Bool
badFn 0 = True
badFn _ = False

{-@ goodFn :: One -> Bool @-}
goodFn :: Int -> Bool
goodFn 1 = goodDep 2
goodFn _ = False

{-@ goodDep :: Two -> Bool @-}
goodDep :: Int -> Bool
goodDep 2 = True
goodDep _ = False

amazingAlgorithm :: (Bool, Bool)
amazingAlgorithm = (goodFn 1, badFn 1)
