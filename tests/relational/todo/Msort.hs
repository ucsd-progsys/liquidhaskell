module Fixme where

{-@ data Tick a = T { res :: a, time :: Int} @-}
data Tick a = T { res :: a, time :: Int}

{-@ data Split = S { l :: [Int], r :: [Int] } @-}
data Split = S { l :: [Int], r :: [Int] }

{-@ assume bsplit :: xs:[Int] -> {v:Tick Split|len xs / 2 <= len (l (res v)) && len (l (res v)) <= len xs / 2 + 1
                                        && len (r (res v)) = len xs / 2} @-}
{-@ ignore bsplit @-}
bsplit :: [Int] -> Tick Split
bsplit = undefined

{-@ ignore merge @-}
merge :: [Int] -> [Int] -> Tick [Int]
merge = undefined

{-@ relational msort ~ msort :: xs1:_ -> _ ~ xs2:_ -> _ ~~ diff xs1 xs2  @-}
msort :: [Int] -> Tick [Int]
msort [] = T [] 0
msort [x] = T [x] 1
msort xs@(_:_:_) = T xs' (tsplit + tmerge)
    where 
		T (S ls rs) tsplit = bsplit xs
		T xs' tmerge = merge (msort ls) (msort rs)) 0
        
{-
fix msort(z). lam f. Lam. Lam. lam l. caseL l of 
   nil   => nil
 | h::tl => caseL tl of 
   	    nil     => h::nil
	  | h'::tl' => let r = bsplit () [] [] l in
	    	       unpack r as y in
		       clet y as x in
		       let r1 = (msort () f [] [] (fst x)) in
		       let r2 = (msort () f [] [] (snd x)) in
	  	       merge () f [] [] r1 r2

<= 0 : 
B (unitR => (B (U ((int X int) [max,0]-> bool, (int X int) [min,0]-> bool))) =>
forall i; alpha.
(list [i, alpha] U int) [diff, sum(minpowlin (alpha, i), {0, cl(log (i))})] -> U (list [i] int)
)
-}