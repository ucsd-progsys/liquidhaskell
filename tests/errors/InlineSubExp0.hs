{-@ LIQUID "--expect-error-containing=== f B C" @-}

-- https://github.com/ucsd-progsys/liquidhaskell/issues/1258

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--short-names" @-} 

module InlineSubExp0 where

import Language.Haskell.Liquid.ProofCombinators 

data Foo = A | B
data Bar = C | D
data Baz = E | F

{-@ reflect f @-}
f :: Foo -> Bar -> Baz
f B C = F
f _ _ = E

{-@ prop :: {f B C == F} @-}
prop = f B C === E *** QED  
