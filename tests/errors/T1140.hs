{-@ LIQUID "--expect-error-containing=Specified type does not refine Haskell type for `T1140.foo`" @-}

module T1140 where

data Label = Label Int 

type Proof = () 

{-@ foo :: Label -> Label -> Label -> Proof @-} 
foo :: Label -> Label -> Label -> Proof -> Proof 
foo a b c v = ()

