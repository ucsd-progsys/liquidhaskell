
\begin{code}

import Prelude hiding (length)
data List a = Emp | (:+:) a (List a)

{-@ measure length @-}
{-@ length :: List a -> Int  @-}
length :: List a -> Int 
length Emp = 0 
length (xs :+: xss) = 1 + length xss

{-@ measure nestedSize @-}
{-@ nestedSize :: List (List a) -> Nat @-}
nestedSize :: List (List a) -> Int
nestedSize Emp = 0
nestedSize (xs :+: xss) = length xs + nestedSize xss
\end{code}