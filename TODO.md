TODO
====

SMTLIB2 (Haskell)
-----------------

Implement an SMTLIB2 query interface directly in Haskell
i.e. port external/fixpoint/smtlib2.ml to haskell


Lazy Instantiation (done?)
--------------------------

Instead of greedily instantiating ALL wf constraints up front, 
do them the *first* time that a corresponding subc constraint 
is solved.

1. change solution so each
	
	kv |-> BOT + [Qual]

2. initialize solution so EACH 

	kv |-> BOT

3. normalize wf so there is UNIQUE wf for kv

	(a)	G  |- k[e1/x1]...[en/xn] ~~~> ? |- k		[ASSUME]

	(b)	G1 |- k,...,Gn |- k	 ~~~> /\Gi |- k

4. build index

	kv |-> normalized-wf 

5. update solver-loop to be lazy 

	(a) if lhs-kv = BOT then DEFER constraint (i.e. prior to is-contra)
	(b) if rhs-kv = BOT then trigger instantiation first with
	(c) instantiate_with :: dom:[Symbol] -> θ:subst -> γ:env -> κ:kvar -> [qual] -> [qual] 


6. let instantiate_with xs θ γ κ qs = qs_
     where 
       γ_  = [b | b@(y, _) <- γ, θy `elem` xs]
       qs_ = instantiate γ_ qs   
      

Failing 10 tests
Failed 10 tests: 
neg/PairMeasure.hs,
neg/ex0-unsafe.hs,
neg/foldN.hs,
neg/foldN1.hs,
pos/PairMeasure.hs,
pos/ptr2.hs,
pos/rangeAdt.hs,
pos/rec_annot_go.hs,
pos/typeAliasDup.hs,
pos/vector2.hs 

issue -- malformed LHS predicate. Why do those predicates get past the actual WF-constraint?
(in orig non-lazy there was a mega pass -- refine_sort -- that pruned away such
qs from the solution -- BEFORE the actual refinement began, i.e. as part of wf.)
hard to do lazily as you have to update all the dependencies -- i.e. push the
affected constraints onto the worklist (where affected = the kvars that got
weakened even though they were on LHS.)

SO: try to figure out WHY this even happens...

 
