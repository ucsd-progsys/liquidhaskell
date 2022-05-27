module StateConstraints where




data ST s a = ST {runState :: s -> (a,s)}

{-@ data ST s a <p :: s -> Bool, q :: s -> s -> Bool, r :: s -> a -> Bool> 
      = ST (runState :: x:s<p> -> (a<r x>, s<q x>)) @-}

 {-@ runState :: forall <p :: s -> Bool, q :: s -> s -> Bool, r :: s -> a -> Bool>. ST <p, q, r> s a -> x:s<p> -> (a<r x>, s<q x>) @-}



{-
cmp :: forall < pref :: s -> Bool, postf :: s -> s -> Bool
              , pre  :: s -> Bool, postg :: s -> s -> Bool
              , post :: s -> s -> Bool
              , rg   :: s -> a -> Bool
              , rf   :: s -> b -> Bool
              , r    :: s -> b -> Bool
              >. 
       {xx::s<pre>, w::s<postg xx> |- s<postf w> <: s<post xx>}
       {ww::s<pre> |- s<postg ww> <: s<pref>}
       (ST <pre, postg, rg> s a)
    -> (ST <pref, postf, rf> s b)
    -> (ST <pre, post, r> s b)
@-}

cmp :: (ST s a)
    -> (ST s b)
    -> (ST s b)

cmp (ST g) (ST f) = ST (\x -> case g x of {(_, s) -> f s})    

{-@ 
bind :: forall < pref :: s -> Bool, postf :: s -> s -> Bool
              , pre  :: s -> Bool, postg :: s -> s -> Bool
              , post :: s -> s -> Bool
              , rg   :: s -> a -> Bool
              , rf   :: s -> b -> Bool
              , r    :: s -> b -> Bool
              , pref0 :: a -> Bool 
              >. 
       {x::s<pre> |- a<rg x> <: a<pref0>}      
       {x::s<pre>, y::s<postg x> |- b<rf y> <: b<r x>}
       {xx::s<pre>, w::s<postg xx> |- s<postf w> <: s<post xx>}
       {ww::s<pre> |- s<postg ww> <: s<pref>}
       (ST <pre, postg, rg> s a)
    -> (a<pref0> -> ST <pref, postf, rf> s b)
    -> (ST <pre, post, r> s b)
@-}

bind :: (ST s a)
    -> (a -> ST s b)
    -> (ST s b)

bind (ST g) f = ST (\x -> case g x of {(y, s) -> (runState (f y)) s})    

{-@ incr :: ST <{\x -> x >= 0}, {\x v -> v = x + 1}, {\x v -> v = x}>  Nat Nat @-}
incr :: ST Int Int
incr = ST $ \x ->  (x, x + 1)

{-@ incr2 :: ST <{\x -> x >= 0}, {\x v -> v = x + 2}, {\x v -> v = x + 1}>  Nat Nat @-}
incr2 :: ST Int Int
incr2 = bind incr (\_ -> incr)


{-@ incr3 :: ST <{\x -> x >= 0}, {\x v -> v = x + 3}, {\x v -> v = x + 2}>  Nat Nat @-}
incr3 :: ST Int Int
incr3 = bind (bind incr (\_ -> incr)) (\_ -> incr)


foo :: (Int, Int)
{-@ foo :: ({v:Nat |  v = 2}, {v:Nat |  v = 3}) @-}
foo = (runState incr3) 0





































