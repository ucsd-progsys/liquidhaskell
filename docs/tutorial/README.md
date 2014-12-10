# LiquidHaskell Tutorial

1. Install
   + Z3
   + Ocaml
   + cabal install
   + emacs

2. Refinement Types
   + Basic: Nat, Pos, Rng
   + Functions: Die, Div, avg2, avg3, scale

3. Polymorphism & HOFs

   + Polymorphism
	 + Lists
	 
   + HOFs
	 + map, fold,...

		title: "Refinement Types 101"
		title: "Bounding Vectors"

000-Refinements.hs

data Grade  = Grade Letter Off
data Letter = A | B | C | D
data Offset = Plus | Minus | None 

letterScore :: Letter -> Rng 40 90
offScore    :: Off    -> Rng 0  10
score       :: Grade  -> Rng 1  100

4. Measures

	Boolean
	+ Nat   : Even/Odd/Value?

	Integer
	+ Lists : head, tail, null
	+ Lists : len: map, append, filter, foldr1, average
   
		title: "Safely Catching A List By Its Tail"

	EXERCISE: do the above examples using PROP valued measure.
	
	Sets
   + Example: Eval.hs
	
5. Case Study: Kmeans

		title: "KMeans Clustering I"

5. Sets
   + Data.Set
	    title: "talking about sets"

   
6. Case Study: AlphaConvert (tests/pos/alphaconvert-List.hs) 

7. Abstract Refinements
  + Copy from FLOPS/IHP talk sequence

8. Termination
  + Copy from BLOG/PAPER sequence
  + HW Exercises


9. Case Study: Low-level Pointers

10. Case Study: Red-Black

11. Case Study: Weighted Biased Heaps


elems        :: [a] -> Set a
elems ([])   = Set.empty
elems (x:xs) = Set.union (Set.singleton x) (elems xs)

len :: [a] -> Set a
len ([])   = Set.empty
len  (x:xs) = 1 GHC.BASE.THIS.THAT.+ len xs

