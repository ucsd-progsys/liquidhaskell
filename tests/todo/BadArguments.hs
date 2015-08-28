import Prelude hiding (init)

data List a = Emp               -- Nil
            | (:::) a (List a)  -- Cons


{-@ init :: (Int -> a) -> n:Nat -> List a n @-}
init :: (Int -> a) -> Int -> List a
init _ 0 = Emp
init f n = f n ::: init f (n-1)
