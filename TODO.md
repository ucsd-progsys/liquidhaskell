TODO
====

Lazy Instantiation
------------------

Instead of greedily instantiating ALL wf constraints up front, 
do them the *first* time that a corresponding subc constraint 
is solved.

1. change solution so each
	
	kv |-> BOT + [Qual]

2. initialize solution so EACH 

	kv |-> BOT

3. normalize wf so there is UNIQUE wf for kv

	(a)	G  |- k[e1/x1]...[en/xn] ~~~> ? |- k		[ASSUME]

	(b)	G1 |- k,...,Gn |- k	~~~> /\Gi |- k

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
      

* change soln type
	* initial solution

* build wf index
	* normalize wf

* update solver loop
	* is_lhs_bot
	* instantiate_with
