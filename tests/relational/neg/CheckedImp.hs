{-@ LIQUID "--expect-any-error" @-}
module CheckedImp where

{-
0; <foo ~ foo : x1 = x2 !=> r1 x1 = r2 x2> |- 1 ~ 1
0; 0 |- + ~ +
-------------
0; 0 |- foo ~ foo
-}
{-@ relational foo ~ foo :: {x1:_ -> y1:_ -> _ ~ x2:_ -> y2:_ -> _ | true !=> x1 = x2 !=> r1 x1 y1 = r2 x2 y2} @-}
foo :: Int -> Int -> Int
foo x _ = x + 1

-- consTotalHOPred (1:[]) (2:[]) ((_, [x1]):vs1) ((_, [x2]):vs2) 
            --     (ERChecked (x1 = x2) (r1 x1 = r2 x2)) []
{-@ relational bar ~ baz :: {_ -> _ ~ _ -> _ | true :=> true} @-}
bar, baz :: Int -> Int
bar _ = foo 1 0
baz _ = foo 2 0
