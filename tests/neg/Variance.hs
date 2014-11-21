module Variance where

{-@ data variance Foo invariant bivariant covariant contravariant @-}
data Foo a b c d



{-@ check_covariant :: Foo a b {v:Int | v > 0} c -> Foo a b {v:Int | v = 1} c @-}
check_covariant :: Foo a b Int c -> Foo a b Int c
check_covariant r = r

{-@ check_contravariant :: Foo a b c {v:Int | v = 1} -> Foo a b c {v:Int | v > 0 } @-}
check_contravariant :: Foo a b c Int-> Foo a b c Int
check_contravariant r = r

{-@ check_bivariant :: Foo a {v: Int | v > 0 } c d -> Foo a {v:Int | ((v > 0) && (v < 2))} c d @-}
check_bivariant :: Foo a Int c d -> Foo a Int c d
check_bivariant r = r


{-@ check_invariant :: Foo {v: Int | v = 1} b c d -> Foo {v:Int | ((v > 0) && (v < 3))} b c d @-}
check_invariant :: Foo Int b c d -> Foo Int b c d
check_invariant r = r



















