{-@ LIQUID "--exactdc"     @-}
{-@ LIQUID "--higherorder" @-}

module T1106 where

import T1106Defs 

import Language.Haskell.Liquid.ProofCombinators

data Foo a = Foo a 
  deriving Eq

{-@ reflect mapFoo @-}
mapFoo :: (b1 -> b2) -> Foo b1 -> Foo b2
mapFoo f (Foo b) = Foo (f b)

thmRef :: (Eq b) => b -> c -> (c -> b -> b) -> ()
{-@ 
thmRef :: b:b -> c:c 
    -> f:(c -> b -> b) 
    -> {mapFoo (bar c) (Foo b) = Foo (bar c b)}
  @-}
thmRef b c f
  = mapFoo (bar c) (Foo b) == Foo (bar c b) *** QED 

thmVar :: (Eq b) => b -> c -> (c -> b -> b) -> ()
{-@ 
thmVar :: b:b -> c:c 
    -> f:(c -> b -> b) 
    -> {mapFoo (f c) (Foo b) = Foo (f c b)}
  @-}
thmVar b c f
  = mapFoo (f c) (Foo b) == Foo (f c b) *** QED 

thmImp :: (Eq b) => b -> c -> (c -> b -> b) -> ()
{-@ 
thmImp :: b:b -> c:c 
    -> f:(c -> b -> b) 
    -> {mapFoo (foo c) (Foo b) = Foo (foo c b)}
  @-}
thmImp b c f
  = mapFoo (foo c) (Foo b) == Foo (foo c b) *** QED 




{-@reflect bar @-}
bar c t = t  