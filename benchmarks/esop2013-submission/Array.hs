{-@ LIQUID "--no-termination" @-}

module LiquidArray where

import Language.Haskell.Liquid.Prelude (liquidAssume)

data Vec a = V (Int -> a)
{-@
data Vec a <dom :: Int -> Prop, rng :: Int -> a -> Prop>
     = V {a :: i:Int<dom> -> a <rng i>}
  @-}


{-@ empty :: forall <p :: Int -> a -> Prop>. Vec <{\v -> 0=1}, p> a @-}
empty     :: Vec  a
empty     = V $ \_ -> (error "Empty array!")


{-@ create :: x:a -> Vec <{\v -> 0=0}, {\i v-> v=x}> a @-}
create     :: a -> Vec  a
create x   = V $ \_ -> x

{-@ get :: forall a <r :: x0: Int -> x1: a -> Prop, d :: x0: Int -> Prop>.
             i: Int<d> ->
             a: Vec<d, r> a ->
             a<r i> @-}
get :: Int -> Vec a -> a
get i (V f) = f i

{-@ set :: forall a <r :: x0: Int -> x1: a -> Prop, d :: x0: Int -> Prop>.
      i: Int<d> ->
      x: a<r i> ->
      a: Vec <{v:Int<d> | v != i}, r> a -> 
      Vec <d, r> a @-}
set :: Int -> a -> Vec a -> Vec a
set i v (V f) = V $ \k -> if k == i then v else f k


-------------------------------------------------------------------------------
---------------------------- init array  --------------------------------------
-------------------------------------------------------------------------------

{-@ zero ::
      i: {v: Int | v >= 0} ->
      n: Int ->
      a: Vec <{\v -> (0 <= v && v < i)}, {\d v -> v = 0}> Int ->
      Vec <{\v -> (0 <= v && v < n)}, {\d v ->  v = 0}> Int @-}
zero :: Int -> Int -> Vec Int -> Vec Int
zero i n a = if i >= n then a
                       else zero (i + 1) n (set i 0 a)
{-@ tenZeroes :: Vec <{\v ->  (0 <= v && v < 10)}, {\d v ->  v = 0}> Int  @-}
tenZeroes = zero z ten empty
  where z   = 0
        ten = 10 

{-@ zeroBackwards ::
      i: Int ->
      n: {v: Int | v > i} ->
      a: Vec <{\v ->  (i < v && v < n)}, {\d v ->  v = 0}> Int ->
      Vec <{\v ->  (0 <= v && v < n)}, {\d v ->  v = 0}> Int @-}
zeroBackwards :: Int -> Int -> Vec Int ->  Vec Int
zeroBackwards i n a = if i < 0 then a
                               else zeroBackwards (i - 1) n (set i 0 a)


{-@ tenZeroes' :: Vec <{\v -> (0 <= v && v < 10)}, {\d v -> v = 0}> Int @-}
tenZeroes' :: Vec Int
tenZeroes' = zeroBackwards nine ten empty
  where nine = 9
        ten  = 10

{-@ zeroEveryOther ::
      i: {v: Int | (v >= 0 && v mod 2 = 0)} ->
      n: Int ->
      a: Vec <{\v -> (0 <= v && v < i && v mod 2 = 0)}, {\d v -> v = 0}> Int ->
      Vec <{\v ->  (0 <= v && v < n && v mod 2 = 0)}, {\d v -> v = 0}> Int @-}
zeroEveryOther :: Int -> Int -> Vec Int -> Vec Int
zeroEveryOther i n a = if i >= n then a
                       else zeroEveryOther (i + 2) n (set i 0 a)

{-@ stridedZeroes ::
      Vec <{\v -> (v mod 2 = 0 && 0 <= v && v < 10)}, {\d v -> v = 0}> Int @-}
stridedZeroes :: Vec Int
stridedZeroes = zeroEveryOther z ten empty
  where z     = 0
        ten   = 10

{-@ initArray :: forall a <p :: x0: Int -> x1: a -> Prop>.
      f: Vec <{\v ->  0=0}, p> a ->
      i: {v: Int | v >= 0} ->
      n: Int ->
      a: Vec <{\v -> (0 <= v && v < i)}, p> a ->
      Vec <{\v -> (0 <= v && v < n)}, p> a  @-}
initArray :: Vec a -> Int -> Int -> Vec a -> Vec a
initArray (V f) i n a = if i >= n then a
                              else initArray (V f) (i + 1) n (set i (f i) a)

{-@ zeroInitArray ::
      i: {v: Int | v >= 0} ->
      n: Int ->
      a: Vec <{\v -> (0 <= v && v < i)}, {\d v -> v = 0}> Int ->
      Vec <{\v -> (0 <= v && v < n)}, {\d v ->  v = 0}> Int @-}
zeroInitArray :: Int -> Int -> Vec Int -> Vec Int
zeroInitArray = initArray (V (\_ ->  0))

{-@ tenZeroes'' :: Vec <{\v -> (0 <= v && v < 10)}, {\d v -> v = 0}> Int @-}
tenZeroes'' :: Vec Int
tenZeroes'' = zeroInitArray z ten empty
  where z   = 0
        ten = 10 

{-@ initid ::
      i: {v: Int | v >= 0} ->
      n: Int ->
      a: Vec <{\v -> (0 <= v && v < i)}, {\j v -> v = j}> Int ->
      Vec <{\v -> (0 <= v && v < n)}, {\k v ->  v = k}> Int @-}
initid :: Int -> Int -> Vec Int -> Vec Int
initid = initArray (V id)

-------------------------------------------------------------------------------
---------------------------- null terms  --------------------------------------
-------------------------------------------------------------------------------


{-@ upperCaseString ::
      n: {v: Int | v > 0} ->
      s: Vec <{\v -> (0 <= v && v < n)}, {\j v -> (j = n - 1 => v = 0)}> Int ->
      Vec <{\v -> (0 <= v && v < n)}, {\j v -> (j = n - 1 => v = 0)}> Int
@-}
upperCaseString :: Int -> Vec Int -> Vec Int
upperCaseString n s = upperCaseString' n 0 s
  where
    upperCaseString' n i s =
      let c = get i s in
      if c == 0 then s
                else upperCaseString' n (i + 1) (set i (c + 32) s)



-------------------------------------------------------------------------------
---------------------------- memoization --------------------------------------
-------------------------------------------------------------------------------
{-@ measure fib :: Int -> Int @-}
{-@ type FibV = Vec <{\v -> 0=0}, {\j v -> ((v != 0) => (v = fib(j)))}> Int @-}


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

