module Pair () where 

import Language.Haskell.Liquid.Prelude 

{-@ data Pair a b <p :: a -> b -> Prop> = P (x :: a) (y :: b<p x>) @-} 
data Pair a b = P a b

incr x = let p = P x ((x+1)) in p
chk (P x (y)) = liquidAssertB (x == y) 
prop  = chk $ incr n
  where n = choose 0

incr2 x = 
  let p1 = (P True (x+1)) in 
  let p2 = P x p1 in 
   p2
chk2 (P x w) = 
   case w of (P z y) -> liquidAssertB (x == y) 
prop2  = chk2 $ incr2 n
  where n = choose 0

incr3 x = P x (P True (P 0 (x+1)))
chk3 (P x (P _(P _ y))) = liquidAssertB (x == y) 
prop3  = chk3 $ incr3 n
  where n = choose 0
