{- TODO: We need an automated test for DiffCheck. That said, our current
   testing infrastructure isn't set up to test internals, so I'd have to
   jimmy-rig it to work. Meanwhile, it has been decided (rightfully) that
   the mechanism I had planned on using was an affront to all that is good,
   and was fixed as a bug. So this test is now pointless. That said, it
   should serve as the basis for a good test in the future, so I think we
   should perserve it for posterity. What follows is my original plan for
   this test.

   Test diffcheck. Has been rigged with a saved diff in .liquid in the
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

-- These guys aren't involved in the above, and should be ignored
-- by DiffCheck

{-@ innocentBystander :: One -> Bool @-}
innocentBystander :: Int -> Bool
innocentBystander 1 = goodSamaritan 1
innocentBystander _ = True

{-@ goodSamaritan :: One -> Bool @-}
goodSamaritan :: Int -> Bool
goodSamaritan 1 = True
goodSamaritan _ = False
