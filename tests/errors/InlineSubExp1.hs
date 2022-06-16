{-@ LIQUID "--expect-error-containing== f B (g A)" @-}

-- https://github.com/ucsd-progsys/liquidhaskell/issues/1258

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--short-names" @-}

module InlineSubExp1 where

import Language.Haskell.Liquid.ProofCombinators 

data Foo = A | B
data Bar = C | D
data Baz = E | F | G 

{-@ reflect f @-}
f :: Foo -> Bar -> Baz
f B C = F
f A D = E
f _ _ = G 

{-@ reflect g @-}
g :: Foo -> Bar 
g A = C 
g _ = D 

test = f B (g A) === f A D *** QED  
