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
      

1. change soln type (solve.ml?)
	* initial solution

2. build wf index 
	* normalize wf

3. update solver loop
	* is_lhs_bot
	* instantiate_with


**263 failing tests, due to:**

Missing filter in inst_ext_sorted. Ok, because filtering happens in SubC humph,
pretty dreadful as likely blows up initial solution.

1. add filtering to inst_ext_sorted   <------------- HEREHEREHEREHERE
    + tests pass?
2. add filtering to RHS cands anyway?
    + tests should pass!
3. add sort-based instantiation


        |> Misc.flap   (inst_qual env ys (A.eVar vv))
--->    |> Misc.filter (wellformed_qual wf env' <&&> C.filter_of_wf wf)
        |> Misc.cross_product ks
 
 
let inst_ext_sorted qs wf = 
  let _    = Misc.display_tick ()               in
  let r    = C.reft_of_wf wf                    in 
  let ks   = List.map snd <| C.kvars_of_reft r  in
  let env  = C.env_of_wf wf                     in
  let vv   = fst3 r                             in
  let t    = snd3 r                             in
  let yts  = inst_binds env                     in
  qs |> Misc.flap (inst_qual_sorted yts vv t)
     |> Misc.cross_product ks
     
let inst_ext qs wf = 
  let _    = Misc.display_tick () in
  let r    = C.reft_of_wf wf in 
  let ks   = C.kvars_of_reft r |> List.map snd in
  let env  = C.env_of_wf wf in
  let vv   = fst3 r in
  let t    = snd3 r in
  let ys   = inst_vars env   in
  let env' = Misc.maybe_map C.sort_of_reft <.> C.lookup_env (SM.add vv r env) in
  qs |> List.filter (Q.sort_of_t <+> sort_compat t)
     |> Misc.flap   (inst_qual env ys (A.eVar vv))
 --->     |> Misc.filter (wellformed_qual wf env' <&&> C.filter_of_wf wf)
     |> Misc.cross_product ks



