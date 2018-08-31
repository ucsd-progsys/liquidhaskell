module StateMonad () where


data ST s a = S { act :: (s -> (a, s)) } 

{-@ data ST s a <p :: s -> Bool> 
	= S { act :: (f:s<p> -> (a, s<p>)) } 
  @-}

{-@ foo :: forall <p:: s -> Bool>. x:a -> ST <p> s {v:a|v=x} @-}
foo ::  a -> ST s a
foo x = S (\s -> (x, s))


