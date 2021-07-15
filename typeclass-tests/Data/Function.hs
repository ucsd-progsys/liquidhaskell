{-@ LIQUID "--reflection" @-}

module Data.Function where
import Prelude hiding (id)
import Liquid.ProofCombinators

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose g f x = g (f x)

{-@ reflect apply @-}
apply :: (a -> b) -> a -> b
apply f x = f x

{-@ reflect flip @-}
flip :: (a -> b -> c) -> b -> a -> c
flip f b a = f a b

{-@ reflect const @-}
const :: a -> b -> a
const x _ = x

{-@ composeId :: f:(a -> b) -> {compose id f == f && compose f id == f} @-}
composeId :: (a -> b) -> ()
composeId f = (axiomExt (compose id f) f $ \x -> compose id f x `cast` ()) `cast`
              (axiomExt (compose f id) f $ \x -> compose f id x `cast` ())


{-@ composeAssoc :: f:(c -> d) -> g:(b -> c) -> h:(a -> b) -> { compose f (compose g h) == compose (compose f g) h  } @-}
composeAssoc :: (c -> d) -> (b -> c) -> (a -> b) -> ()
composeAssoc f g h = axiomExt (compose (compose f g) h) (compose f (compose g h)) $ \a ->
  compose (compose f g) h a `cast`
  f (g (h a)) `cast`
  compose f (compose g h) a `cast`
  ()
