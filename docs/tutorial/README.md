# LiquidHaskell Tutorial

0. Install

--- Part I: Refinement Types

1. Refinement Types

2. Polymorphism & HOFs

3. Refining Datatypes

--- Part II: Measures

4. Propositions

5. Numbers [TODO] **<--- HEREHEREHEREHERE** 

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
	+ EX: "map-reduce"

6. Sets [TODO]
    + Example: Eval.hs
    EX: write a `noDup` measure
	EX: write a `nub`  function

--- Part III : Applications & Case Studies

7. Case Study: Totality

8. Case Study: Termination
  + Copy from BLOG/PAPER sequence
  + HW Exercises

9. Case Study: Red-Black Trees **OR** Weighted Biased Heaps [TODO]
  + EX: AVL TREE (insert/delete/member)
   
10. Case Study: Low-level Pointers [TODO]

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


\begin{code}
-- SHOW zipWith
-- SHOW dotProd
-- SHOW matMult (using dotProd/transpose)

-- EX: write sig for take, drop
-- EX: what is the SIG for reverseHelper s.t. reverse checks?

{-@ reverse :: xs:List a -> ListN a (size xs) @-}
reverse xs = reverseHelper xs N

reverseHelper N acc          = acc
reverseHelper (x :+: xs) acc = reverseHelper xs (x :+: acc)

{- EX: given IMPLEMENTATIONS

   split  :: a -> [a] -> [[a]]
   join   :: a -> [[a]] -> [a]
   assert :: {v:Bool | Prop v} -> a -> a

   WRITE TYPES TO VERIFY:

   prop_join_split str c = assert (size s == size s') ()
     where
        s'               = join c (split s c)
 -}

{-@ type ListN a N = {v:List a | size v = N} @-}

{-@ type Grid a N M = ListN (ListN a M) N    @-}

{- EX: write a function

   transpose :: n:Nat -> m:Nat -> Grid a n m -> Grid a m n
-}

{- EX: write a function kmeans (using map-reduce) -}

\end{code}

LINKS 

+ Case Study 1: AlphaConvert (tests/pos/alphaconvert-List.hs) 
+ Case Study 2: Kmeans


