
-- https://github.com/ucsd-progsys/liquidhaskell/issues/1258

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--short-names" @-} 

module T1258 where 

import Language.Haskell.Liquid.NewProofCombinators 

data Foo = A | B
data Bar = C | D
data Baz = E | F

{-@ reflect f @-}
f :: Foo -> Bar -> Baz
f B C = F
f _ _ = E

{-@ prop :: {f B C == F} @-}
prop = f B C === E *** QED  
