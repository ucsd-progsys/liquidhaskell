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

--- **HEREHEREHERE**

3. Refining Datatypes

data Sparse =
data List a = Nil | Cons { hd :: a, tl :: [{v:a | hd <= v}] }
data Heap a = ...
data BST a  = ...


--- Part II: Measures

4. Propositions
http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/

    Prop	
    + head, tail, null

    + len: map, append, foldr1, wtAverage (!)

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


\begin{code}
data List a = N | (:+:) a (List a)

infixr 9 :+:

{- invariant {v:List a | 0 <= size v} @-}
{-@ measure size @-}
{-@ size :: List a -> Nat @-}
size :: List a -> Int  
size N          = 0
size (_ :+: xs) = 1 + size xs

{-@ type NEList a = {v:List a | size v > 0} @-} 

{-@ head :: NEList a -> a @-} 
head (x :+: _) = x
head N         = die "head: N"

-- EX: what is a signature for `null` such that `safeHead` typechecks
safeHead xs
  | null xs   = Nothing
  | otherwise = Just $ head xs 

{-@ null :: xs:List a -> {v:_ | Prop v <=> size xs = 0} @-}
null N = True
null _ = False

-- SHOW map, foldr, foldr1, wtAverage (BAD), wtAverage (GOOD)

-- EX: risers

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


