Refinement Types For Haskell
============================

 {#berg} 
--------

<br>

+ Niki Vazou
+ Eric Seidel
+ *Ranjit Jhala*

<br>

**UC San Diego**

<div class="hidden">

\begin{code}
main = putStrLn "Easter Egg"
\end{code}

</div>

Well-Typed Programs *Can* Go Very Wrong
=======================================

Division By Zero
----------------

\begin{code} _ 
λ> let average xs = sum xs `div` length xs

λ> average [1,2,3]
2
\end{code}

<div class="fragment"> 

\begin{code} _ 
λ> average []
*** Exception: divide by zero
\end{code}

</div>


