module T1556 where

{-@ type Alias a b = (a,b) @-}
type Alias a b = (a,b)

{-@ foo :: Alias (a,b) a @-}
foo ::  Alias (a,b) a
foo = undefined 
