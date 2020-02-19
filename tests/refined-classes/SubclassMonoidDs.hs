{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module SemigroupDs where

import Prelude hiding (Semigroup, mappend)



{-@ data MySemigroup a = CMySemigroup {
    mappend :: a -> a -> a, 
    lawAssociative :: x:a -> y:a -> z:a -> {mappend x (mappend y z) == mappend (mappend x y) z} } @-}

data MySemigroup a = CMySemigroup{
    mappend :: a -> a -> a,
    lawAssociative :: a -> a -> a -> ()}

{-@ data MyMonoid a = CMyMonoid {
     p1MyMonoid :: MySemigroup a,
     mempty :: a,
     lawEmpty :: x:a -> {mappend p1MyMonoid x mempty == x && mappend p1MyMonoid mempty x == x}}
@-}

data MyMonoid a = CMyMonoid {
     p1MyMonoid :: MySemigroup a,
     mempty :: a,
     lawEmpty :: a -> ()
     }

{-@ monoidAssoc :: dMyMonoid:MyMonoid a -> a:a -> b:a -> c:a ->
 {mappend (p1MyMonoid dMyMonoid) (mappend (p1MyMonoid dMyMonoid) a b) c /=
  mappend (p1MyMonoid dMyMonoid) a (mappend (p1MyMonoid dMyMonoid) b c)} @-}
monoidAssoc :: MyMonoid a -> a -> a -> a -> ()
monoidAssoc dMyMonoid =
  let dMySemigroup = p1MyMonoid dMyMonoid in
    \a b c -> lawAssociative dMySemigroup a b c
