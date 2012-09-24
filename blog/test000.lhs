
Liquid Types
============

This is the **very first** blog entry on the subject of liquid types.

First, some boring bits, such as

\begin{code}
module Abs where

import Language.Haskell.Liquid.Prelude  (liquidAssert)
\end{code}

Ok. With that out of the way, lets look at a *tres* simple function.

\begin{code}
{-@ abz :: x:Int -> {v: Int | v >= 0} @-}
abz :: Int -> Int
abz x | x > 0     = x
      | otherwise = (0 - x)
\end{code}

Now, a little something to test the mouseover highlighting. Put your mouse
over `abz` below for bedazzlement.

\begin{code}
{-@ prop_abz :: Int -> Int @-}
prop_abz z = liquidAssert (z' >= 0) z' 
  where z' = abz z
\end{code}

That's all folks!
