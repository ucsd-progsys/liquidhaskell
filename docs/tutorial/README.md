# LiquidHaskell Tutorial

0. Install
   + Z3
   + Ocaml
   + cabal install
   + emacs

--- Part I: Refinement Types

1. Refinement Types
   + Basic: Nat, Pos, Rng
   + Functions: Die, Div, avg2, avg3, scale

2. Polymorphism & HOFs

   BLOG: "Bounding Vectors"
   
   + Polymorphism
	 + Lists
	 
   + HOFs
	 + map, fold,...
		title: "Bounding Vectors"

3. Refining Datatypes

data Sparse =
data List a = Nil | Cons { hd :: a, tl :: [{v:a | hd <= v}] }
data Heap a = ...
data BST a  = ...

--- **HEREHEREHERE**

--- Part II: Measures

4. Propositions
http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/

    Prop	
    + head, tail, null
	+ len: map, append, filter, foldr1,wtAverage (!)
	+ EX: risers
	+ EX: "map-reduce"

5. Numbers 

	Int
    + zipWith
	+ dotProd
	+ insertSort
    + quickSort // partition :: (a -> Bool) -> xs:[a] -> Pair (List a) (List a) / len (fst v) + len (snd v) = len xs
    data Pair a b = { fst :: a, snd :: b}

	+ EX: take/drop
    + EX: append/reverse
    + EX:prop_join_split

	+ EX: transpose
	+ EX: matMult
    + EX: data Matrix a = { rows :: Nat
	                      , cols :: Nat
		        		  , elts :: Grid a rows cols }
					
	+ EX: kmeans-using-"map-reduce"

6. Sets
    + Example: Eval.hs
    EX: write a `noDup` measure
	EX: write a `nub`  function

--- Part III : Applications & Case Studies

7. Case Study: Totality

8. Case Study: Termination

  + Copy from BLOG/PAPER sequence
  + HW Exercises

9. Case Study: Red-Black Trees **OR** Weighted Biased Heaps
  + EX: AVL TREE (insert/delete/member)
   
10. Case Study: Low-level Pointers

--- Part IV : Abstract Refinements 

11. Abstract Refinements I (code)
  + Copy from FLOPS/IHP talk sequence
  + Vanilla/Code [compose, foldr, ...]

12. Abstract Refinements II (data)
  + RecRef [List, BST]
  + Arrays

13. Abstract Refinements III (constraints)
  + compose
  + filter
  + state 

