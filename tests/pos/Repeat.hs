module Foo where
import Prelude hiding (repeat, take)

data L a = N | C a (L a)

{-@
data L a <p :: (L a) -> Prop>
  = N
  | C (x::a) (xs::L <p> a <<p>>)
@-}

{-@
measure isCons :: L a -> Prop
isCons (N)     = false
isCons (C a l) = true
@-}

{-@ type Stream a = {v: L <{\v -> (isCons v)}> a | (isCons v)} @-}

{-@ Lazy repeat @-}
{-@ repeat :: a -> Stream a @-}
repeat :: a -> L a
repeat x = C x (repeat x)

{-@ take :: Nat -> Stream a -> L a @-}
take :: Int -> L a -> L a
take 0 _           = N
take n ys@(C x xs) = x `C` take (n-1) xs
