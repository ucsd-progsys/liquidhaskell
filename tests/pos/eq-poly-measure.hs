module Pair () where 

import Language.Haskell.Liquid.Prelude 

{-@ data Thing a = P (unThing :: a) @-} 
data Thing a = P a

property :: Bool
property = chk t1 
  where 
  chk (P x) = liquidAssertB x 

  t1 :: Thing Bool 
  t1 = P True 
