# LiquidHaskell Tutorial

1. Install
   + Z3
   + Ocaml
   + cabal install
   + emacs

2. Refinement Types
   + Basic: Nat, Pos, Rng
   + Functions: Die, Div, avg2, avg3, scale
   + Polymorphism:
   + Containers: Lists, Maps,...
   + HOFs: map, fold,...

		title: "Refinement Types 101"
		title: "Bounding Vectors"

000-Refinements.hs

data Grade  = Grade Letter Off
data Letter = A | B | C | D
data Offset = Plus | Minus | None 

letterScore :: Letter -> Rng 40 90
offScore    :: Off    -> Rng 0  10
score       :: Grade  -> Rng 1  100

3. Measures

   + Nat   : Even/Odd
   + Lists : head, tail, null
   + Lists : len: map, append, filter

		title: "Safely Catching A List By Its Tail"

4. Case Study: Kmeans

		title: "KMeans Clustering I"

5. Sets
   + Data.Set
	    title: "talking about sets"

   + Example: Eval.hs
   
6. Case Study: AlphaConvert (tests/pos/alphaconvert-List.hs) 

7. Abstract Refinements
  + Copy from FLOPS/IHP talk sequence

8. Termination
  + Copy from BLOG/PAPER sequence
  + HW Exercises


9. Case Study: Low-level Pointers

10. Case Study: Red-Black

11. Case Study: Weighted Biased Heaps
