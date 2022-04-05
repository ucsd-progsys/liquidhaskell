module SynchLisis where

-- {-@ prefSum :: Int -> [Nat] -> Nat @-}
-- prefSum :: Int -> [Int] -> Int
-- prefSum n _ | n <= 0 = 0
-- prefSum _ []         = 0
-- prefSum n (x : xs)   = 1 + prefSum (n - 1) xs

-- {-@ relational prefSum ~ prefSum :: n:Int -> xs:_ -> _ ~ m:Int -> ys:_ -> _ 
--                                  ~~ n = m => xs = ys => r1 n xs <= r2 m ys @-}


{-@ hasEvenLen :: [Int] -> {v:Bool|v} @-}
hasEvenLen :: [Int] -> Bool
hasEvenLen []       = True
hasEvenLen (x : xs) = let b = hasEvenLen xs in if b then False else True

{-
I. l1 = [], l2 = [] |- True ~ True | true => r1 = r2

II. l1 = [], l2 = (x2 : xs2), hasEvenLen xs |- True ~ False | true => r1 = r2

III. l1 = [], l2 = (x2 : xs2), !hasEvenLen xs |- True ~ True | true => r1 = r2

III. l1 = [], l2 = (x : xs), hasEvenLen xs |- True ~ False | true => r1 = r2

IV. l1 = (x1 : xs1), l2 = (x : xs), hasEvenLen xs |- True ~ False | true => r1 = r2

-}

-- {-@ relational hasEvenLen ~ hasEvenLen :: xs:[Int] -> Bool ~ ys:[Int] -> Bool 
--                                        ~~ true => r1 xs == r2 ys @-}
