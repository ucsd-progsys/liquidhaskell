{-@ LIQUID "--expect-any-error" @-}
module SndOrdPred where

{-@ assume relational foo ~ foo :: {x1:_ -> _ ~ x2:_ -> _ 
                         | x1 < x2 :=> r1 < r2} @-}
-- x1 < x2 :=> r1 x1 > r2 x2
foo :: Int -> Int
foo x = x

{-@ assume relational bar ~ bar :: {f1:(x1':_ -> _) -> x1:_ -> _ 
                          ~ f2:(x2':_ -> _) -> x2:_ -> _ 
                         | (x1' < x2' => r1 < r2) :=> x1 < x2 :=> r1 f1 x1 < r2 f2 x2} @-}
bar :: (Int -> Int) -> Int -> Int
bar f x = f (x + 1)

{-@ assume relational bar' ~ bar' :: {x1:_ -> f1:(x1':_ -> _) -> _ 
                          ~ x2:_ -> f2:(x2':_ -> _) -> _ 
                         | x1 < x2 :=> (x1' < x2' => r1 < r2) :=> r1 x1 f1 < r2 x2 f2} @-}
bar' :: Int -> (Int -> Int) -> Int
bar' x f = f (x + 1)

{-
                u1 :=> v1           v2 :=> u2
                (-1) ~ (-1) | v1 :=> v2 (syn)       
            --------------------------------
            (-1) ~ (-1) | u1 :=> u2  (chk)        x ~ x | x1 < x2
 
 bar ~ bar | (x1' < x2' :=> r1 x1' < r2 x2') :=> x1 < x2 :=> r1 x1 <= r2 x2
 ------------------------------------------------------------------------
 bar (-1) x ~ bar (-1) x | (x1' < x2' :=> true && true :=> f1 x1' < f2 x2') :=> r1 < r2 (syn)           


 |- (h1 && h2 :=> p) || h1 :=> p || h2 :=> p || true :=> p
 
 
 (x1' < x2' :=> x1' < x2' && f1 x1' < f2 x2' :=> f1 x1' < f2 x2') :=> r1 < r2 |- p
 ------------------------------------------------------------------------------
 bar (-1) x ~ bar (-1) x | true (chk) -}

{-@  relational baz ~ baz :: {x1:Int -> Int ~ x2:Int -> Int | true :=> true} @-}
baz :: Int -> Int
baz x = bar' x foo

