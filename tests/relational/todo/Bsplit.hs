module Fixme where

{-@ data Tick a = T { res :: a, time :: Int} @-}
data Tick a = T { res :: a, time :: Int}

-- instance Monad Tick where
--   (T r t) >>= f = let T r' t' = f r in T r' (t + t')
-- instance Functor Tick
-- instance Applicative Tick

-- {-@ reflect tick @-}
-- tick :: Int -> a -> Tick a
-- tick n a = T a n

{-@ reflect diff @-}
{-@ diff :: xs:[Int] -> ys:{[Int]|len ys == len xs} -> Int @-}
diff :: [Int] -> [Int] -> Int
diff (x : xs) (y : ys) | x == y = diff xs ys
diff (x : xs) (y : ys) | x /= y = 1 + diff xs ys
diff _ _                        = 0

{-@ data Split = S { l :: [Int], r :: [Int] } @-}
data Split = S { l :: [Int], r :: [Int] }

{-@ bsplit :: xs:[Int] -> {v:Tick Split|len xs / 2 <= len (l (res v)) && len (l (res v)) <= len xs / 2 + 1
                                        && len (r (res v)) = len xs / 2} @-}
bsplit :: [Int] -> Tick Split
bsplit []  = T (S [] []) 0
bsplit [x] = T (S [x] []) 1
bsplit (x : y : xs) =
  let T (S ls rs) t = bsplit xs in T (S (x : ls) (y : rs)) (t + 2)

{-@ relational bsplit ~ bsplit :: xs1:_ -> _ ~ xs2:_ -> _
                               ~~ true => diff xs1 xs2 == 
                                             diff (l (res (r1 xs1))) ((r (res (r1 xs1))))
                                                + diff (l (res (r2 xs2))) (r (res (r2 xs2))) @-}

