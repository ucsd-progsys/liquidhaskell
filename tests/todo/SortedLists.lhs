\begin{code}
module SortedLists where
\end{code}

I want to prove that in a sorted list every element is `>=` than the head:

\begin{code}
{-@ type SL a = [a]<{\x v -> x <= v}> @-}

{-@ measure head :: [a] -> a
    head (x:xs) = x
  @-}
\end{code}


Turns out that to prove it I have to compose the list using `:`
(liquidHaskell only proves `proveOK`)
\begin{code}
{-@ propOKA, propOKB, propBADA, propBADB, propBADC :: 
      Ord a => xs:(SL a)  -> [{v:a|v >= (head xs)}] 
  @-}
propOKA, propOKB, propBADA, propBADB, propBADC :: 
      Ord a => [a] -> [a]
\end{code}

\begin{code}
propOKA xxs@(x:xs) = x:xs
propOKB xxs@(x:xs) = listID xxs

listID (x:xs) = (x:xs)
listID []     = []
\end{code}

We know that both `x` and `xs` satisfy the desired property 
but polymorphism on `:` is the way to transfer this information to the result.
Any attempt that doesn't use this information fails:
\begin{code}
propBADA xxs@(x:xs) = xxs
propBADB xxs@(x:xs) = id xxs
propBADC xxs@(x:xs) = listID' xxs

{-@ listID' :: forall <p :: a -> a -> Prop> . [a]<p> -> [a]<p> @-}
listID' :: [a] -> [a]
listID' (x:xs) = (x:xs)
listID' []     = []
\end{code}

So, the following version of `merge` fails:

\begin{code}
{-@ LIQUID "--no-termination" @-}
{-@ merge :: Ord a => (SL a) -> (SL a) -> (SL a) @-}
merge :: Ord a => [a] -> [a] -> [a]
merge xxs@(x:xs) yys@(y:ys)
  | x <= y    = x : merge xs yys
  | otherwise = y : merge xxs ys
\end{code}

