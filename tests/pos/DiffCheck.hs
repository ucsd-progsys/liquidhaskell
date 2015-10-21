{- Test diffcheck. Has been rigged with a saved diff in .liquid in the
   following ways:

   1) goodFn has changed from the saved diff.
   2) badFn has not changed from the saved diff.
   3) badFn has violated the invariant of badDep.

   What should happen is: LH will test this file, and will test the
   goodFn and amazingAlgorithm binders. It will see that goodDep has
   not changed and is protected by a liquid type signature, and not
   check it. It will see that badFn has not changed, and is protected
   by a liquid type signature and not check it. LH will return safe,
   having checked only goodFn and amazingAlorithm if the diff logic
   works. If something is broken, it will check badFn and return unsafe. -}

{-@ LIQUID "--diffcheck" @-}

module DiffCheck where

{-@ type Zero = {v:Int | v == 0} @-}
{-@ type One = {v:Int | v == 1} @-}
{-@ type Two = {v:Int | v == 2} @-}
{-@ type Three = {v:Int | v == 3} @-}

{-@ badFn :: Zero -> Bool @-}
badFn :: Int -> Bool
badFn 0 = badDep 0
badFn _ = False

{-@ goodFn :: One -> Bool @-}
goodFn :: Int -> Bool
goodFn 1 = goodDep 2 -- I changed!
goodFn _ = False

{-@ goodDep :: Two -> Bool @-}
goodDep :: Int -> Bool
goodDep 2 = True
goodDep _ = False

{-@ badDep :: Three -> Bool @-}
badDep :: Int -> Bool
badDep 3 = True
badDep _ = False

amazingAlgorithm :: (Bool, Bool)
amazingAlgorithm = (goodFn 1, badFn 0)
