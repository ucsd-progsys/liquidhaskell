module LiquidArray where

import Language.Haskell.Liquid.Prelude (liquidAssume)

{-@ set :: forall a <p :: x0: Int -> x1: a -> Prop, r :: x0: Int -> Prop>.
      i: Int<r> ->
      x: a<p i> ->
      a: (j: {v: Int<r> | v != i} -> a<p j>) ->
      (k: Int<r> -> a<p k>) @-}
set :: Int -> a -> (Int -> a) -> (Int -> a)
set i x a = \k -> if k == i then x else a k

{-@ get :: forall a <p :: x0: Int -> x1: a -> Prop, r :: x0: Int -> Prop>.
             i: Int<r> ->
             a: (j: Int<r> -> a<p j>) ->
             a<p i> @-}
get :: Int -> (Int -> a) -> a
get i a = a i

{-@ empty :: i: {v: Int | 0 = 1} -> a @-}
empty :: Int -> a
empty = const (error "Empty array!")

-------------------------------------------------------------------------------
---------------------------- init array  --------------------------------------
-------------------------------------------------------------------------------

{-@ zero ::
      i: {v: Int | v >= 0} ->
      n: Int ->
      a: (j: {v: Int | (0 <= v && v < i)} -> {v: Int | v = 0}) ->
      (k: {v: Int | (0 <= v && v < n)} -> {v: Int | v = 0}) @-}
zero :: Int -> Int -> (Int -> Int) -> (Int -> Int)
zero i n a = if i >= n then a
                       else zero (i + 1) n (set i 0 a)

{-@ tenZeroes :: i: {v: Int | (0 <= v && v < 10)} -> {v: Int | v = 0} @-}
tenZeroes = zero z ten empty
  where z   = 0
        ten = 10 


{-@ zeroBackwards ::
      i: Int ->
      n: {v: Int | v > i} ->
      a: (j: {v: Int | (i < v && v < n)} -> {v: Int | v = 0}) ->
      (k: {v: Int | (0 <= v && v < n)} -> {v: Int | v = 0}) @-}
zeroBackwards :: Int -> Int -> (Int -> Int) -> (Int -> Int)
zeroBackwards i n a = if i < 0 then a
                               else zeroBackwards (i - 1) n (set i 0 a)

{-@ tenZeroes' :: i: {v: Int | (0 <= v && v < 10)} -> {v: Int | v = 0} @-}
tenZeroes' = zeroBackwards nine ten empty
  where nine = 9
        ten  = 10

{-@ zeroEveryOther ::
      i: {v: Int | (v >= 0 && v mod 2 = 0)} ->
      n: Int ->
      a: (j: {v: Int | (0 <= v && v < i && v mod 2 = 0)} -> {v: Int | v = 0}) ->
      (k: {v: Int | (0 <= v && v < n && v mod 2 = 0)} -> {v: Int | v = 0}) @-}
zeroEveryOther :: Int -> Int -> (Int -> Int) -> (Int -> Int)
zeroEveryOther i n a = if i >= n then a
                       else zeroEveryOther (i + 2) n (set i 0 a)

{-@ stridedZeroes ::
      j: {v: Int | (v mod 2 = 0 && 0 <= v && v < 10)} -> {v: Int | v = 0} @-}
stridedZeroes = zeroEveryOther z ten empty
  where z     = 0
        ten   = 10

{-@ initArray :: forall a <p :: x0: Int -> x1: a -> Prop>.
      f: (z: Int -> a<p z>) ->
      i: {v: Int | v >= 0} ->
      n: Int ->
      a: (j: {v: Int | (0 <= v && v < i)} -> a<p j>) ->
      (k: {v: Int | (0 <= v && v < n)} -> a<p k>) @-}
initArray f i n a = if i >= n then a
                              else initArray f (i + 1) n (set i (f i) a)

{-@ zeroInitArray ::
      i: {v: Int | v >= 0} ->
      n: Int ->
      a: (j: {v: Int | (0 <= v && v < i)} -> {v: Int | v = 0}) ->
      (k: {v: Int | (0 <= v && v < n)} -> {v: Int | v = 0}) @-}
zeroInitArray :: Int -> Int -> (Int -> Int) -> (Int -> Int)
zeroInitArray = initArray (const 0)

{-@ tenZeroes'' :: i: {v: Int | (0 <= v && v < 10)} -> {v: Int | v = 0} @-}
tenZeroes'' = zeroInitArray z ten empty
  where z   = 0
        ten = 10 

{-@ initid ::
      i: {v: Int | v >= 0} ->
      n: Int ->
      a: (j: {v: Int | (0 <= v && v < i)} -> {v: Int | v = j}) ->
      (k: {v: Int | (0 <= v && v < n)} -> {v: Int | v = k}) @-}
initid :: Int -> Int -> (Int -> Int) -> (Int -> Int)
initid = initArray id

-------------------------------------------------------------------------------
---------------------------- null terms  --------------------------------------
-------------------------------------------------------------------------------

upperCaseString' :: Int -> Int -> (Int -> Int) -> (Int -> Int)
upperCaseString' n i s =
  let c = get i s in
  if c == 0 then s
            else upperCaseString' n (i + 1) (set i (c + 32) s)

{-@ upperCaseString ::
      n: {v: Int | v > 0} ->
      s: (j: {v : Int | (0 <= v && v < n)} ->
          {v: Int | (j = n - 1 => v = 0)}) ->
      (j: {v : Int | (0 <= v && v < n)} ->
       {v: Int | (j = n - 1 => v = 0)})
@-}
upperCaseString :: Int -> (Int -> Int) -> (Int -> Int)
upperCaseString n s = upperCaseString' n 0 s

-------------------------------------------------------------------------------
---------------------------- memoization --------------------------------------
-------------------------------------------------------------------------------


-------------------------------------------------------------------------------
---------------------------- memoization --------------------------------------
-------------------------------------------------------------------------------

{-@ measure fib :: Int -> Int @-}
{-@ type FibV = j:Int -> {v:Int| ((v != 0) => (v = fib(j)))} @-}

{-@ assume axiom_fib :: i:Int -> {v: Bool | (Prop(v) <=> (fib(i) = ((i <= 1) ? 1 : ((fib(i-1)) + (fib(i-2)))))) } @-}
axiom_fib :: Int -> Bool
axiom_fib i = undefined

{-@ fastFib :: x:Int -> {v:Int | v = fib(x)} @-}
fastFib     :: Int -> Int
fastFib n   = snd $ fibMemo (\_ -> 0) n

{-@ fibMemo :: FibV -> i:Int -> (FibV, {v: Int | v = fib(i)}) @-}
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










