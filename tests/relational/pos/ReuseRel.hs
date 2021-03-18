l :: [Int] -> Int 
l [] = 0
l (_:xs) = 1 + l xs 

{-@ relational l ~ l :: xs:_ -> _ ~ ys:_ -> _ 
                     ~~ len xs == len ys => (r1 xs) == (r2 ys) @-}

foo :: [Int] -> Int
foo [] = l []
foo (_:xs) = foo xs

{-@ relational foo ~ foo :: xs:_ -> _ ~ ys:_ -> _ ~~ len xs == len ys => (r1 xs) == (r2 ys) @-}