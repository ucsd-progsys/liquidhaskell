module ScopeCheck where


-- CAUSES PROBLEMS, I don't know how this is represented internally with
-- the FSREFT and all that...
{-@ foo :: a -> (a, [a])<\goo -> {v: [{v: a | v = goo}] | true }> @-}
foo :: a -> (a, [a])
foo x = (x, [x])

-- THIS IS FINE
{-@ moo :: a -> [a]<\goo -> {v: a | v = goo}> @-}
moo x = [x, x, x]
