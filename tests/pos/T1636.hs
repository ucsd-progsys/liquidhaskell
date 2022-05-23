{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module T1636 where

data RA a  = RA  


{-@ type RRA a E1 E2 = {v:RA a | E1 == E2} @-}


{-@ assume eqRTCtx :: f:a -> g:a  -> RRA a {f} {g} -> ctx:(a -> b) -> RRA b {ctx f} {ctx g}  @-}
eqRTCtx ::  a -> a -> RA a -> (a -> b) -> RA b
eqRTCtx _f _g _pf _ctx = undefined  

fEqG0BadDomain :: Integer -> RA Integer
fEqG0BadDomain x = RA

{-@ reflect f @-}
f :: Integer -> Integer 
f x = x + 1 

{-@ reflect g @-}
g :: Integer -> Integer 
g x = x + 1 
