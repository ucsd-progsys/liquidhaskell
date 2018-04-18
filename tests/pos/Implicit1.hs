{-@ type IntN N = {v:Int | v = N} @-}

-- AT:TODO: Incr works around the fact that the parser doesn't like addition. It's infix, I guess.
--   /home/anish/src/liquidhaskell/tests/pos/Implicit1.hs:3:39: Error: Cannot parse specification:
-- 
--   3 | {-@ foo ::  (() -> IntN n) -> IntN (n + 1) @-}
--                                             ^
-- 
--       unexpected "+"
--       expecting bareTyArgP
-- 
-- 
--   /home/anish/src/liquidhaskell/tests/pos/Implicit1.hs:10:31: Error: Cannot parse specification:
-- 
--   10 | {-@ test2 :: m:Int -> IntN (m + 1) @-}
--                                      ^
-- 
--       unexpected "+"
--       expecting bareTyArgP
-- 
-- 
--   /home/anish/src/liquidhaskell/tests/pos/Implicit1.hs:13:31: Error: Cannot parse specification:
-- 
--   13 | {-@ test3 :: m:Int -> IntN (m + 2) @-}
--                                      ^
-- 
--       unexpected "+"
--       expecting bareTyArgP

{-@ inline incr @-}
incr :: Int ->Int
incr x = x + 1

{-@ foo :: n:Int ~> (() -> IntN n) -> IntN (incr n) @-}
foo :: (() -> Int) -> Int
foo f = 1 + f ()

{-@ test1 :: IntN 11 @-}
test1 = foo (\_ -> 10)

{-@ test2 :: m:Int -> IntN (incr m) @-}
test2 m = foo (\_ -> m)

{-@ test3 :: m:Int -> IntN (incr (incr m)) @-}
test3 m = foo (\_ -> m+1)

{-@ test4 :: IntN 11 @-}
test4 = foo (const (10))

{-@ bar :: IntN 3 @-}
bar = foo (\_ -> foo (\_ -> 1))
