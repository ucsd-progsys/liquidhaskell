> {-@ LIQUID "--no-termination" @-}
> {-@ LIQUID "--totality"       @-}
> {-@ LIQUID "--diffcheck"      @-}
> 
> module Totality where
> 
> import Prelude hiding (head)
> import Language.Haskell.Liquid.Prelude
> import Control.Exception.Base

One of the most maligned Haskell functions is also one of the simplest.

> head (x:_) = x

Many people argue that `head` and co. should be removed from the Prelude because
they're partial functions, and partial functions are dangerous.

The often-recommended alternative of making partial functions return a `Maybe` or
`Either` is often tedious and encourages the use of *other* partial functions like `fromJust`.

What we really ought to do is *prove* that undefined case can never arise.

This is relatively easy in LiquidHaskell.

GHC already does much of the heavy lifting by filling in all of the undefined
cases with explicit calls to various error functions, e.g.

< head (x:_) = x

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

> {-@ head :: {v:[a] | 0 < len v} -> a @-}

Now, when LiquidHaskell sees the case-analysis on the `[]` case, it puts

< len xs = 0

in the environemnt as usual, *but* we just gave `head` a pre-condition that

< len xs > 0

So we actually end up with

< len xs = 0 && len xs > 0

which is a contradiction, therefore it is safe to "call" `patError` since we 
have proven that the call will never *actually* happen.


Partial Zipping
---------------

Inside LiquidHaskell, we often want to combine multiple lists, so we use the 
stalwart `zipWith` function. The problem with `zipWith` is that if the two 
lists are *not* the same size, it will *silently drop* the remaining items of 
the longer list.

This is almost *never* what we want, instead we consider it an error to call 
`zipWith` on lists of non-equal length. So we've written our own `safeZipWith` 
function that leaves the case of zipping a nil and a cons undefined.

> safeZipWith f = go
>   where
>     go (x:xs) (y:ys) = f x y : go xs ys
>     go []     []     = []

As you can see, LiquidHaskell is not happy with this definition! It (rightly) 
complains that we've left a case unhandled because we haven't yet told it that 
we only want `safeZipWith` to accept lists of equal length. Luckily, this is 
easily rectified, we'll introduce a handy type-alias for a list with the same
length as another list

> {-@ type ListL a Xs = {v:[a] | len v == len Xs} @-} 

and use it to concisely express our contract for `safeZipWith`.

> {-@ safeZipWith :: (a -> b -> c) -> xs:[a] -> ListL b xs -> ListL c xs @-}


Totality in Real-World
----------------------

If that was not convincing enough, I'll leave you with a final example from 
HsColour, which is probably invoked thousands of times per day.

> nestcomment :: Int -> String -> (String, String)
> nestcomment n ('{':'-':ss) | n>=0 = (("{-"++   cs),rm)
>                                   where (cs,rm) = nestcomment (n+1) ss
> nestcomment n ('-':'}':ss) | n>0  = let (cs,rm) = nestcomment (n-1) ss
>                                     in (("-}"++cs),rm)
> nestcomment n ('-':'}':ss) | n==0 = ("-}",ss)
> nestcomment n (s:ss)       | n>=0 = ((s:cs),rm)
>                                   where (cs,rm) = nestcomment n ss
> nestcomment n [] = ([],[])

What this function does precisely is not that important, notice instead that 
LiquidHaskell has flagged it as partial, because there's an unhandled case

< nestcomment n (s:ss) | n < 0 = ????

Well, it doesn't seem particularly sensible to have a *negative* nesting depth, 
so we'll just tell LiquidHaskell that `nestcomment` should really only be 
called with natural numbers (without incurring the wrath of Peano numbers)!

> {-@ nestcomment :: Nat -> _ -> (_,_) @-}


So that was totality, next let's try something more ambitious, proving memory 
safety in `ByteString`!
