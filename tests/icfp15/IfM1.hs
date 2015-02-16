module Ex1 (ifM) where

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}


{-@ data RIO a <pre :: World -> Prop, post :: World -> a -> World -> Prop, p:: a -> Prop> 
  = RIO (rs :: (x:World<pre> -> (a<p>, World)<\w -> {v:World<post x w> | true}>))
  @-}
data RIO a  = RIO {runState :: World -> (a, World)}

{-@ runState :: forall <pre :: World -> Prop, post :: World -> a -> World -> Prop, p::a -> Prop>. 
                RIO <pre, post, p> a -> x:World<pre> -> (a<p>, World)<\w -> {v:World<post x w> | true}> @-}

data World  = W


{-@
ifM  :: forall < pre   :: World -> Prop 
               , p :: World -> Bool -> World -> Prop
               , r1 :: World -> Prop
               , r2 :: World -> Prop
               , q :: Bool -> Prop
               , post1 :: World -> a -> World -> Prop
               , post  :: World -> a -> World -> Prop>.                  
       {b :: {v:Bool<q> | Prop v},   w :: World<pre>    |- World<p w b>      <: World<r1>        } 
       {b :: {v:Bool<q> | not (Prop v)},   w :: World<pre>    |- World<p w b>      <: World<r2>        } 
       {w1::World<pre>, w2::World, y::a|- World<post1 w2 y> <: World<post w1 y>}
          RIO <pre, p, q> Bool 
       -> RIO <r1, post1, {\v -> true}> a
       -> RIO <r2, post1, {\v -> true}> a
       -> RIO <pre, post, {\v -> true}> a
@-}
ifM :: RIO Bool -> RIO a -> RIO a -> RIO a
ifM (RIO cond) e1 e2 
  = RIO $ \x -> case cond x of {(y, s) -> runState (if y then e1 else e2) s} 

{-@ measure counter :: World -> Int @-}

get :: RIO Int 
{-@ get :: forall <p :: World -> Prop >. 
       RIO <p,\w x -> {v:World<p> | x = counter v && v == w}, {\v -> true}> Int @-} 
get = undefined 



{-@ f :: n:Int -> RIO <{v:World | counter v = n}, \w1 b -> {v:World |  (Prop b => n /= 0) && (Prop b => counter v /= 0)}, {\v -> true}> {v:Bool | Prop v <=> n /= 0} @-}
f :: Int -> RIO Bool
f = \x -> ret (x /= 0)


divX       :: RIO Int 
{- divX   :: RIO <{\w -> (counter w) /= 0 }, {\w1 x w2 -> (counter w1) /= 0 && (counter w2) /= 0}, {\v -> true}> Int @-}
divX       = get `bind` bar 



bar :: Int -> RIO Int
{-@ bar :: {v:Int | v /= 0} -> RIO Int @-}
bar = \x -> ret (100 `div` x)

ifTest     :: RIO Int
{-@ ifTest     :: RIO Int @-}
ifTest     = ifM (checkZeroX) (divX) (ret 10)
  where 
    checkZeroX = get `bind` \x -> ret (x /= 0)
    divX       = get `bind` \x -> ret (100 `div` x)



{-@ checkZeroX :: RIO <{\x -> true}, {\w1 b w2 -> Prop b => counter w2 /= 0}, {\v -> true}> Bool @-}
checkZeroX :: RIO Bool
checkZeroX = get `bind` f 





{-@ bind :: forall < pre   :: World -> Prop 
               , pre2  :: a -> World -> Prop 
               , p     :: a -> Prop
               , pp    :: a -> Prop
               , q     :: b -> Prop
               , post1 :: World -> a -> World -> Prop
               , post2 :: a -> World -> b -> World -> Prop
               , post :: World -> b -> World -> Prop>.
       {x::a<p>, w::World<pre>|- World<post1 w x> <: World<pre2 x>}
       {y::a, w::World<pre>, w2::World<pre2 y>, x::b, y::a<p> |- World<post2 y w2 x> <: World<post w x>}     
       {x::a, w::World, w2::World<post1 w x>|- {v:a | v = x} <: a<p>}   
       RIO <pre, post1, pp> a
    -> (x:a<p> -> RIO <{v:World<pre2 x> | true}, \w1 y -> {v:World<post2 x w1 y> | true}, q> b)
    -> RIO <pre, post, q> b @-}

bind :: RIO a -> (a -> RIO b) -> RIO b
bind (RIO g) f = RIO $ \x -> case g x of {(y, s) -> (runState (f y)) s} 



{-@ ret :: forall <p :: World -> Prop>.
           x:a -> RIO <p, \w0 y -> {w1:World<p> | w0 == w1 && y == x }, {\v -> v = x}> a
  @-}  
ret w      = RIO $ \x -> (w, x)


