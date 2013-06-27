module LiquidArray where

import Language.Haskell.Liquid.Prelude (liquidAssume)

-- |Indexed-Dependent Refinements

data Vec a = V (Int -> a)

{-@
data Vec a <dom :: Int -> Prop, rng :: Int -> a -> Prop>
     = V {a :: i:Int<dom> -> a <rng i>}
  @-}

-- Describing interesting vectors:

{-@ type IdVec = 
     Vec <{\v -> (v < 100)}, {\j v -> (v = j)}> Int
  @-}

{-@ type ZeroTerm N = 
     Vec <{\v -> (0 <= v && v < N)}, {\j v -> (j = N - 1 => v = 0)}> Int
  @-}

{-@ measure fib :: Int -> Int @-}

{-@ type FibV = 
     Vec <{\v -> 0=0}, {\j v -> ((v != 0) => (v = fib(j)))}> Int @-}


-- |Operations on Vectors

{-@ empty :: forall <p :: Int -> a -> Prop>. Vec <{\v -> 0=1}, p> a @-}
empty     :: Vec  a
empty     = V $ \_ -> (error "Empty array!")

{-@ get :: forall a <r :: Int -> a -> Prop, d :: Int -> Prop>.
             i: Int<d> ->
             a: Vec<d, r> a ->
             a<r i> @-}
get :: Int -> Vec a -> a
get i (V f) = f i

{-@ set :: forall a <r :: Int -> a -> Prop, d :: Int -> Prop>.
      i: Int<d> ->
      x: a<r i> ->
      a: Vec <{v:Int<d> | v != i}, r> a -> 
      Vec <d, r> a @-}
set :: Int -> a -> Vec a -> Vec a
set i v (V f) = V $ \k -> if k == i then v else f k

-- | Using Vectors

{-@ assume axiom_fib :: i:Int -> {v: Bool | (Prop(v) <=> (fib(i) = ((i <= 1) ? 1 : ((fib(i-1)) + (fib(i-2)))))) } @-}
axiom_fib :: Int -> Bool
axiom_fib i = undefined

{-@ fastFib :: x:Int -> {v:Int | v = fib(x)} @-}
fastFib     :: Int -> Int
fastFib n   = snd $ fibMemo (V (\_ -> 0)) n


{-@ fibMemo :: FibV -> i:Int -> (FibV, {v: Int | v = fib(i)}) @-}
fibMemo :: Vec Int -> Int -> (Vec Int, Int)
fibMemo t i 
  | i <= 1    
  = (t, liquidAssume (axiom_fib i) (1 :: Int))
  
  | otherwise 
  = case get i t of   
      0 -> let (t1, n1) = fibMemo t  (i-1)
               (t2, n2) = fibMemo t1 (i-2)
               n        = liquidAssume (axiom_fib i) (n1 + n2)
           in  (set i n t2,  n)
      n -> (t, n)
