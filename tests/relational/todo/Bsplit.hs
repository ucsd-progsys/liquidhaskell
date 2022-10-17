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

-- {-@ bsplit :: xs:[Int] -> {v:Tick Split|len xs / 2 <= len (l (res v)) && len (l (res v)) <= len xs / 2 + 1
--                                         && len (r (res v)) = len xs / 2} @-}
-- bsplit :: [Int] -> Tick Split
-- bsplit []  = T (S [] []) 0
-- bsplit [x] = T (S [x] []) 1
-- bsplit (x : y : xs) =
--   let T (S ls rs) t = bsplit xs in T (S (x : ls) (y : rs)) (t + 2)

-- {-@ relational bsplit ~ bsplit :: xs1:_ -> _ ~ xs2:_ -> _
--                                ~~ true => Fixme.diff xs1 xs2 == 
--                                              Fixme.diff (Fixme.l (Fixme.res (r1 xs1))) ((Fixme.l (Fixme.res (r2 xs2))))
--                                                 + Fixme.diff (Fixme.r (Fixme.res (r1 xs1))) (Fixme.r (Fixme.res (r2 xs2))) @-}

bsplit' :: [Int] -> Split
bsplit' []  = S [] []
bsplit' [x] = S [x] []
bsplit' (x : y : xs) =
  let S ls rs = bsplit' xs in S (x : ls) (y : rs)

{-@ relational bsplit' ~ bsplit' :: xs1:_ -> _ ~ xs2:_ -> _
                               ~~ true => Fixme.diff xs1 xs2 == 
                                             Fixme.diff (Fixme.l ((r1 xs1))) ((Fixme.l ((r2 xs2))))
                                                + Fixme.diff (Fixme.r ((r1 xs1))) (Fixme.r ((r2 xs2))) @-}

