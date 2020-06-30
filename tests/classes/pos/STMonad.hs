-- TAG: classes 
-- TAG: bounds 

{-@ LIQUID "--no-pattern-inline" @-}
{-@ LIQUID "--higherorder"       @-}

module STMonad where

data ST s a = S {runSt :: s -> (a, s) }

{-@ data ST s a <pre :: s -> Bool, post :: a -> s -> Bool>
       = S { runSt :: (x:s<pre> -> ((a, s)<post>)) }
  @-}

{-@ apply :: forall <p :: s -> Bool, q :: a -> s -> Bool>.
               ST <p, q> s a -> s<p> -> (a, s)<q>
  @-}
apply :: ST s a -> s -> (a, s)
apply (S f) s = f s

instance Functor (ST s) where
  fmap = undefined

instance Applicative (ST s) where
  pure  = undefined
  (<*>) = undefined

instance Monad (ST s) where
  {-@ instance Monad (ST s) where
        return :: forall <p :: a -> s -> Bool>. x:a -> ST <{v:s<p x>| true}, p, {v:a | true}> s a ;
        >>=    :: forall <pbind :: s -> Bool, qbind :: a -> s -> Bool, rbind :: b -> s -> Bool>.
                                  ST <pbind, qbind> s a
                              -> (xbind:a -> ST <{v:s<qbind xbind> | true}, rbind> s b)
                              -> ST <pbind, rbind> s b;
        >>    :: forall <pbind :: s -> Bool, qbind :: a -> s -> Bool, rbind :: b -> s -> Bool>.
                                 ST <pbind, qbind> s a
                              -> (ST <{v:s| true}, rbind> s b)
                              -> ST <pbind, rbind> s b
    @-}
  return x    = S $ \s -> (x, s)
  (S m) >> k  = S $ \s -> let (a, s') = m s in apply k s'
  (S m) >>= k = S $ \s -> let (a, s') = m s in apply (k a) s'

--------------------------------------------------------------------------------

{-@ fresh :: forall <pre :: Int -> Bool>.
                    { zoo::Int |- Int<pre> <: {v:Int | 0 <= v} }
                    ST <pre, {\rv v -> ( 0 <= rv && rv + 1 = v )}> Int (Int<pre>)
  @-}

{- fresh :: ST <{\v -> (0 <= v)}, {\rv v -> ( 0 <= rv && rv + 1 = v )}> Int Nat @-}
fresh :: ST Int Int
fresh = S (\n -> (n, n+1))

--------------------------------------------------------------------------------

{-@ incr0 :: ST <{\v -> (0 <= v)}, {\rv v -> (0 <= rv && 1 <= v)}> Int Int @-}
incr0 :: ST Int Int
incr0 = do
  n <- fresh
  return n

{-@ incr1 :: ST <{\v -> (0 <= v)}, {\rv v -> (0 <= rv && 1 <= v)}> Int Int @-}
incr1 :: ST Int Int
incr1 = fresh >>= return

{-@ incr2 :: ST <{\v -> (0 == v)}, {\rv v -> (4 == v)}> Int Int @-}
incr2 :: ST Int Int
incr2 = do
  n0 <- fresh
  n1 <- fresh
  n2 <- fresh
  n3 <- fresh
  return (checkEq 3 n3)

{-@ checkEq :: x:Int -> y:{Int | y = x} -> {v:Int | v = y} @-}
checkEq :: Int -> Int -> Int
checkEq x y = y
