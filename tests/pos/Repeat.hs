module Foo where
import Prelude hiding (repeat)

data L a = N | C a (L a)

{-@ data L a <p :: (L a) -> Prop>
 = N
 | C (x::a) (xs::(L <p> a))
  @-}

repeat :: a -> L a
repeat x = C x $ repeat x
