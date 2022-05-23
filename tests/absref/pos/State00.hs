module State00 () where

data ST s = S { act :: s -> s } 

{-@ data ST s <p :: s -> Bool> = S { act :: (s<p> -> s<p>) } @-}

{-@ foo :: forall <q :: sip -> Bool>. ST <q> sip @-}
foo :: ST s
foo = S (\s -> s)
