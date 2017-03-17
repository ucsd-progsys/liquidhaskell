
--
-- The MoCC of Signal in Haskell (clocked)
-- Jean-Pierre.Talpin@inria.fr 12/3/15
--

Module Signals where

-- an event is (now) present with a value or (determined) absent

data Event a = absent | now a

-- a signal is a (non empty?) lazy list of events 
-- type Signal a = {v: [Event a] | len(v) > 0}

type Signal a = [Event a]

-- the clock of a signal 

measure clk :: a Signal -> Bool
clk (absent : _) = false
clk ((now _) : _) = true

-- the value of a signal 

measure val :: a Signal -> a
val ((now v) : _) = v

-- not defined if absent ... how to say that val v => clk v ?

-- feedback: pre initially returns w and then the stored head of x
-- pre's, y's and w property should be a fixpoint p
--
--      {-@ pre :: forall <p :: Prop>. Signal a<p> -> a<p> -> Signal a<p> @-}
--
-- p should contain clk x = clk pre here just true

pre :: Signal a -> a -> Signal a
pre (x as ((now v) : _) w = (now w) : pre x v
pre (x as (absent  : _) w =  absent : pre x w
infix pre

-- synchronous sample à la Lustre

{-@ sample :: x:Signal a -> y:Signal Bool -> {v:Signal a| clk v = clk x = clk y} @-}

sample :: Signal a -> Signal Bool -> Signal a
sample ((now v) : x) ((now True)  : y) = v : sample x y
sample ((now _) : x) ((now False) : y) = absent : sample x y
sample (absent  : x) (absent      : y) = absent : sample x y

-- synchronous merge à la Lustre

{-@ merge :: x:Signal Bool -> y:Signal a -> z:Signal a -> {v:Signal a| clk v = clk x = clk y = clk z} @-}

merge :: Signal Bool -> Signal a -> Signal a -> Signal a
merge ((now True)  : x) ((now v) : y) ((now _) : z) = v : merge x y z
merge ((now False) : x) ((now _) : y) ((now v) : z) = v : merge x y z
merge (absent      : x) (absent  : y) (absent  : z) = absent : merge x y z

-- sample à la Signal

{-@ when :: x:Signal a -> y:Signal Bool -> {v:Signal a| clk v = clk x and val y} @-}

when :: Signal a -> Signal Bool -> Signal a
when ((now v) : x) ((now True)  : y) = v : when x y
when (_       : x) ((now False) : y) = absent : when x y
when (_       : x) (absent      : y) = absent : when x y

-- merge à la Signal

{-@ combine :: x:Signal Bool -> y:Signal a -> z:Signal a -> {v:Signal a| clk v = clk x or clk y} @-}

combine :: Signal a -> Signal a -> Signal a
combine ((now v) : x) (_ : y) = v : combine x y 
combine (absent  : x) (v : y) = v : combine x y

