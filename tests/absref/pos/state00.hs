module StateMonad () where

data ST s = S { act :: s -> s } 

{-@ data ST s <p :: s -> Bool> = S { act :: (s<p> -> s<p>) } @-}

{-@ foo :: forall <p :: s -> Bool>. ST <p> s @-}
foo :: ST s
foo = S (\s -> s)

{- 
{-@ fooz :: forall <p :: s -> Bool>. s<p> -> s<p> @-}
fooz :: s -> s
fooz = (\s -> s)

{-@ data Boo s <q :: s -> Bool> = B { thing :: s <q> } @-}
data Boo s = B { thing :: s }

{-@ boo :: forall <r :: s -> Bool>. s<r> -> Boo<r> s @-}
boo x = B x 
-}