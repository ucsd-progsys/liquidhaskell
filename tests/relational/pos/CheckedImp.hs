module CheckedImp where

{-@ relational foo ~ foo :: { x1:_ -> _ ~ x2:_ -> _ | x1 = x2 !=> r1 x1 = r2 x2 } @-}
foo :: Int -> Int
foo = (+1)

{-@ relational bar ~ baz :: { _ ~ _ | r1 = r2 } @-}
bar, baz :: Int
bar = foo 1
baz = foo 1