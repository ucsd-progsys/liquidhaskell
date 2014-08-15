> {-@ LIQUID "--no-termination" @-}
> {-@ LIQUID "--totality" @-}
> {-@ LIQUID "-g-package-db" @-}
> {-@ LIQUID "-g/Users/gridaphobe/.nix-profile/lib/ghc-7.8.3/package.conf.d/" @-}
> module Main where
> 
> import Prelude hiding (head)
> import Language.Haskell.Liquid.Prelude
> import Control.Exception.Base

Partial functions are a pain to deal with, they have a tendency to blow up when 
you least expect it. And yet the often-recommended alternative of making 
partial functions return a `Maybe` or `Either` is tedious and encourages the 
use of other partial functions like `fromJust`. What we really ought to do is 
*prove* that undefined case can never arise.

It turns out this is relatively easy in LiquidHaskell. GHC already does much of 
the heavy lifting by filling in all of the undefined cases with explicit calls
to various error functions, e.g.

> head (x:xs) = x

is transformed into

< head xs = case xs of
<   (x:_) = x
<   []    = patError "..."

The path is clear, we want to make LiquidHaskell prove that we will never call 
any of these internal error functions that GHC inserts. We can accomplish this 
by giving each function a refined type where the pre-condition is `false`, i.e.

< {-@ patError :: {v:_ | false} -> a @-}

*If* LiquidHaskell can prove `false` at any of these callsites, it means there 
was a contradiction somewhere along the way and the call is effectively dead 
code. So how do we prove that `patError` is unreachable in `head`?

We can specify that `head` should only be called with *non-empty* lists by 
giving it a refined type like

> {-@ head :: {v:[a] | len v > 0} -> a @-}

Now, when LiquidHaskell sees the case-analysis on the `[]` case, it puts

< len xs = 0

in the environemnt as usual, *but* we just gave `head` a pre-condition that

< len xs > 0

So we actually end up with

< len xs = 0 && len xs > 0

which is a contradiction, therefore it is safe to "call" `patError` since we 
have proven that the call will never *actually* happen.


Map
---

> {-@ nestcomment :: Nat -> xs:_ -> (_,{v:_|(if ((len xs) = 0) then ((len v) = 0) else ((len v) <= (len xs))) }) @-}
> 
> nestcomment :: Int -> String -> (String,String)
> nestcomment n ('{':'-':ss) | n>=0 = (("{-"++cs),rm)
>                                   where (cs,rm) = nestcomment (n+1) ss
> nestcomment n ('-':'}':ss) | n>0  = let (cs,rm) = nestcomment (n-1) ss
>                                     in (("-}"++cs),rm)
> nestcomment n ('-':'}':ss) | n==0 = ("-}",ss)
> nestcomment n (s:ss)       | n>=0 = ((s:cs),rm)
>                                   where (cs,rm) = nestcomment n ss
> nestcomment n [] = ([],[])
