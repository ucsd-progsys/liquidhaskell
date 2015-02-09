\begin{code}
module ICFP15 where

import Prelude hiding ((.), (++),  filter)

{-@ LIQUID "--no-termination" @-}

\end{code}

Function Composition: Bringing Everything into Scope!
-----------------------------------------------------

- Definition

\begin{code}
{-@ 
(.) :: forall <p :: b -> c -> Prop, q :: a -> b -> Prop, r :: a -> c -> Prop>. 
       {x::a, w::b<q x> |- c<p w> <: c<r x>}
       (y:b -> c<p y>)
    -> (z:a -> b<q z>)
    ->  x:a -> c<r x>
@-}    
(.) f g x = f (g x)    
\end{code}

- Usage 

\begin{code}
{-@ plusminus :: n:Nat -> m:Nat -> x:{Nat | x <= m} -> {v:Nat | v = (m - x) + n} @-}
plusminus :: Int -> Int -> Int -> Int
plusminus n m = (n+) . (m-)
\end{code}

- Qualifiers

\begin{code}
{-@ qualif PLUSMINUS(v:int, x:int, y:int, z:int): (v = (x - y) + z) @-}
{-@ qualif PLUS     (v:int, x:int, y:int)       : (v = x + y)       @-}
{-@ qualif MINUS    (v:int, x:int, y:int)       : (v = x - y)       @-}
\end{code}


Appending Sorted Lists
-----------------------
\begin{code}
{-@ type OList a = [a]<{\x v -> v >= x}> @-}

{-@ (++) :: forall <p :: a -> Prop, q :: a -> Prop>.
        {x::a<p> |- a<q> <: {v:a| x <= v}} 
        OList (a<p>) -> OList (a<q>) -> OList a @-}
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)


{-@ qsort :: xs:[a] -> OList a  @-}
qsort []     = []
qsort (x:xs) = (qsort [y | y <- xs, y < x]) ++ (x:(qsort [z | z <- xs, z >= x])) 
\end{code}

Relative Complete
-----------------


\begin{code}
main i = app (check i) i
-- Here p of `app` will be instantiated to 
-- p := \v -> i <= v

{-@ check :: x:Int -> {y:Int | x <= y} -> () @-}
check :: Int -> Int -> ()
check x y | x < y     = () 
          | otherwise = error "oups!"
\end{code}


\begin{code}
{-@ app :: forall <p :: Int -> Prop>. 
           {x::Int<p> |- {v:Int| v = x + 1} <: Int<p>}
           (Int<p> -> ()) -> x:Int<p> -> () @-}
app :: (Int -> ()) -> Int -> ()
app f x = if p x then app f (x + 1) else f x

p :: Int -> Bool
{-@ p :: Int -> Bool @-}
p = undefined
\end{code}

- TODO: compare with related paper

Filter
------

\begin{code}
{-@ filter :: forall <p :: a -> Prop, q :: a -> Bool -> Prop>.
                  {y::a, flag::{v:Bool<q y> | Prop v} |- {v:a | v = y} <: a<p>}
                  (x:a -> Bool<q x>) -> [a] -> [a<p>]
  @-}

filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x       = x : filter f xs
  | otherwise = filter f xs
filter _ []   = []


{-@ measure isPrime :: Int -> Prop @-}
isPrime :: Int -> Bool 
{-@ isPrime :: n:Int -> {v:Bool | Prop v <=> isPrime n} @-}
isPrime = undefined

-- | `positives` works by instantiating:
-- p := \v   -> isPrime v
-- q := \n v -> Prop v <=> isPrime n

	
{-@ primes :: [Int] -> [{v:Int | isPrime v}] @-}
primes     = filter isPrime
\end{code}


- filter in Katalyst:

('R filter) : 
   l -> f: (x -> {v |  v = false => 'R(x) = emp 
                    /\ v = true  => 'R(x) = Rid(x)})
-> {v | Rmem (v) = (Rmem 'R)(l)}


Similar in that the result refinement depends on the 'R.
In our types `p` depends on the `q`.

Precondition constraints the relation 'R  and then post condition 

Differences
Katalyst talks about ordering and not other theories, like linear arithmetic

Similarities 
Bounds can be seen as Abstract Refinement transformers, i.e., higher order Abstract Refinements. 


State
-----

- State's Definition 
\begin{code}
{-@ data RIO a <pre :: World -> Prop, post :: World -> a -> World -> Prop> 
  = RIO (rs :: (x:World<pre> -> (a, World)<\w -> {v:World<post x w> | true}>))
  @-}
data RIO a  = RIO {runState :: World -> (a, World)}

{-@ runState :: forall <pre :: World -> Prop, post :: World -> a -> World -> Prop>. 
                RIO <pre, post> a -> x:World<pre> -> (a, World)<\w -> {v:World<post x w> | true}> @-}

data World  = W

instance Monad RIO where
{-@ instance Monad RIO where
 >>= :: forall < pre   :: World -> Prop 
               , pre2  :: World -> Prop 
               , p     :: a -> Prop
               , post1 :: World -> a -> World -> Prop
               , post2 :: World -> b -> World -> Prop
               , post :: World -> b -> World -> Prop>.
       {w::World<pre>, x::a |- World<post1 w x> <: World<pre2>}        
       {w::World<pre>, y::a, w2::World<post1 w y>, x::b |- World<post2 w2 x> <: World<post w x>}        
       {w::World, x::a|- {v:a | v = x} <: a<p>}
       RIO <pre, post1> a
    -> (a<p> -> RIO <pre2, post2> b)
    -> RIO <pre, post> b ;
 >>  :: forall < pre   :: World -> Prop 
               , pre2  :: World -> Prop 
               , p     :: a -> Prop
               , post1 :: World -> a -> World -> Prop
               , post2 :: World -> b -> World -> Prop
               , post :: World -> b -> World -> Prop>.
       {w::World<pre>, x::a |- World<post1 w x> <: World<pre2>}        
       {w::World<pre>, y::a, w2::World<post1 w y>, x::b |- World<post2 w2 x> <: World<post w x>}        
       RIO <pre, post1> a
    -> RIO <pre2, post2> b
    -> RIO <pre, post> b ;
 return :: forall <p :: World -> Prop>.
           x:a -> RIO <p, \w0 y -> {w1:World<p> | w0 == w1 && y == x }> a
  @-}  
  (RIO g) >>= f = RIO $ \x -> case g x of {(y, s) -> (runState (f y)) s} 
  (RIO g) >>  f = RIO $ \x -> case g x of {(y, s) -> (runState f    ) s}    
  return w      = RIO $ \x -> (w, x)
  fail          = error
\end{code}


- Using the RIO
\begin{code}
{-@ measure counter :: World -> Int @-}

{-@ incr :: RIO <{\x -> counter x >= 0}, {\w1 x w2 -> counter w2 = counter w1 + 1}>  Nat Nat @-}
incr :: RIO Int
incr = undefined
\end{code}

- General State functions: twice
\begin{code}
{-@ appM :: forall <pre :: World -> Prop, post :: World -> a -> World -> Prop>.
           (a -> RIO <pre, post> b) -> a -> RIO <pre, post> b @-}
appM :: (a -> RIO b) -> a -> RIO b
appM f x = f x

{-@ 
twiceM  :: forall < pre   :: World -> Prop 
                 , post1 :: World -> a -> World -> Prop
                 , post :: World -> a -> World -> Prop>.
       {w::World<pre>, x::a |- World<post1 w x> <: World<pre>}        
       {w::World<pre>, y::a, w2::World<post1 w y>, x::a |- World<post1 w2 x> <: World<post w x>}        
       (b -> RIO <pre, post1> a) -> b   
    -> RIO <pre, post> a 
@-}
twiceM :: (b -> RIO a) -> b -> RIO a
twiceM f x = do {f x ; f x}


{-@ incr2 :: RIO <{\x -> counter x >= 0}, {\w1 x w2 -> counter w2 = counter w1 + 2}>  Nat Nat @-}
incr2 :: RIO Int
incr2 = twiceM (\_ -> incr) 0
\end{code}

- if

\begin{code}
{-@ 
ifM  :: forall < pre   :: World -> Prop 
                 , post1 :: World -> () -> World -> Prop
                 , post :: World -> () -> World -> Prop>.
       {w::World<pre>, y::(), w2::World<pre>, x::() |- World<post1 w2 x> <: World<post w x>}             
       RIO <pre, \w1 x -> {v:World<pre> | true}> Bool 
       -> RIO <pre, post1> () 
       -> RIO <pre, post1> ()  
       -> RIO <pre, post> ()
@-}
ifM :: RIO Bool -> RIO () -> RIO () -> RIO ()
ifM guard e1 e2 = do {g <- guard ; if g then e1 else e2}
\end{code}

- while
\begin{code}
-- THIS TYPE CHECKS, BUT HOW CAN WE ACTUALLY USE IT?
{-@ 
whileM  :: forall < pre   :: World -> Prop 
                  , post1 :: World -> () -> World -> Prop
                  , post2 :: World -> () -> World -> Prop
                  , post :: World -> () -> World -> Prop>.
       {w::World<pre>, y::(), w2::World<pre>, x::() |- World<post1 w2 x> <: World<post w x>}             
       {w::World<pre>, x::() |- {v:World | v = w} <: World<post1 w x>}
       {w::World<pre>, x::() |- {v:World | v = w} <: World<post w x>}
       {w::World<pre>, x::() |- World<post w x> <: World<pre>}
       {w1::World, x::Bool |- World<post2 w1 x> <: World<pre>}        
       RIO <pre, post2> Bool 
       -> RIO <pre, post1> () 
       -> RIO <pre, post> ()
@-}
whileM :: RIO Bool -> RIO () -> RIO ()
whileM guard e1 = do {g <- guard ; if g then do {e1; whileM guard e1} else return ()}
\end{code}


- Using whileM
\begin{code}
{-@ measure counter1 :: World -> Int @-}
{-@ measure counter2 :: World -> Int @-}

{-@ incr' :: RIO <{\x -> true}, {\w1 x w2 -> counter1 w2 = counter1 w1 + 1}> () @-}
incr' :: RIO ()
incr' = undefined

{-@ condM :: RIO <{\x -> true}, {\w1 x w2 -> (Prop x) <=> counter1 w2 >= counter2 w2}> Bool @-}
condM :: RIO Bool
condM = undefined

-- NV: TODO
{- prop :: RIO <{\x -> true}, {\w1 x w2 -> counter1 w2 < counter2 w2}> () @-}
prop :: RIO ()
prop = whileM condM incr' 
\end{code}

- TODO: compare with Nik
