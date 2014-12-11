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

   BLOG: "Bounding Vectors"
   
   + Polymorphism
	 + Lists
	 
   + HOFs
	 + map, fold,...

		title: "Bounding Vectors"

4. Measures

    Prop	
    + head, tail, null
	+ len: map, append, filter, foldr1,wtAverage (!)
	+ EX: risers
	+ EX: "map-reduce"
	
	Integer
    + zipWith
	+ dotProd
	+ insertSort
    + quickSort // partition :: (a -> Bool) -> xs:[a] -> Pair (List a) (List a) / len (fst v) + len (snd v) = len xs
    data Pair a b = { fst :: a, snd :: b}

	+ EX: take/drop
	+ EX:prop_join_split

	+ EX: transpose
	+ EX: matMult
    + EX: data Matrix a = { rows :: Nat
	                      , cols :: Nat
		        		  , elts :: Grid a rows cols }
					
	+ EX: kmeans-using-"map-reduce"
	
	Sets
	
    + Example: Eval.hs
   
    EX: write a `noDup` measure
	EX: write a `nub`  function


5. Abstract Refinements

  + Copy from FLOPS/IHP talk sequence

6. Termination

  + Copy from BLOG/PAPER sequence
  + HW Exercises

7. Case Study: Red-Black Trees **OR** Weighted Biased Heaps

   + EX: AVL TREE (insert/delete/member)
   
8. Case Study: Low-level Pointers
