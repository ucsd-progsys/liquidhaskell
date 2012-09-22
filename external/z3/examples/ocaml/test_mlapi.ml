(** Module test_mlapi - ML test and demo program for Z3.  Matches test_capi.ml - JakobL@2007-09-08 *)
(*
   @name Auxiliary Functions
*)

(**
   printf
*)
let printf = Printf.printf;;

(**
   fprintf
*)
let fprintf = Printf.fprintf;;

(**
   Exit gracefully in case of error.
*)
let exitf message = fprintf stderr "BUG: %s.\n" message; exit 1;;

(**
   Create a logical context.  Enable model construction.
   Also enable tracing to stderr.
*)
let mk_context ctx = 
  let ctx = Z3.mk_context_x (Array.append [|("MODEL", "true")|] ctx) in
  (* You may comment out the following line to disable tracing: *)
  Z3.trace_to_stderr ctx;
  ctx;;

(**
   Create a variable using the given name and type.
*)
let mk_var ctx name ty = Z3.mk_const ctx (Z3.mk_string_symbol ctx name) ty;;

(**
   Create a boolean variable using the given name.
*)
let mk_bool_var ctx name = mk_var ctx name (Z3.mk_bool_type ctx);;

(**
   Create an integer variable using the given name.
*)
let mk_int_var ctx name = mk_var ctx name (Z3.mk_int_type ctx);;

(**
   Create a Z3 integer node using a C int. 
*)
let mk_int ctx v = Z3.mk_int ctx v (Z3.mk_int_type ctx);;

(**
   Create a real variable using the given name.
*)
let mk_real_var ctx name = mk_var ctx name (Z3.mk_real_type ctx);;

(**
   Create the unary function application: {e (f x) }.
*)
let mk_unary_app ctx f x = Z3.mk_app ctx f [|x|];;

(**
   Create the binary function application: {e (f x y) }.
*)
let mk_binary_app ctx f x y = Z3.mk_app ctx f [|x;y|];;

(**
   Auxiliary function to check whether two Z3 types are equal or not.
*)
let equal_types ctx t1 t2 = Z3.is_eq ctx (Z3.type_ast_to_ast ctx t1) (Z3.type_ast_to_ast ctx t2);;

(**
   Check whether the logical context is satisfiable, and compare the result with the expected result.
   If the context is satisfiable, then display the model.
*)
let check ctx expected_result =
  begin
    let (result,m) = Z3.check_and_get_model ctx in
    (match result with
    | Z3.L_FALSE -> printf "unsat\n";
    | Z3.L_UNDEF ->
      printf "unknown\n";
      printf "potential model:\n%s\n" (Z3.model_to_string ctx m);
    | Z3.L_TRUE -> printf "sat\n%s\n" (Z3.model_to_string ctx m);
    );
    if result != expected_result then exitf "unexpected result";
  end;;

(**
   Prove that the constraints already asserted into the logical
   context implies the given formula.  The result of the proof is
   displayed.
   Z3 is a satisfiability checker. So, one can prove {e f } by showing
   that {e (not f) } is unsatisfiable.
   The context {e ctx } is not modified by this function.
*)
let prove ctx f is_valid =
  begin
    (* save the current state of the context *)
    Z3.push ctx;

    let not_f = Z3.mk_not ctx f in
    Z3.assert_cnstr ctx not_f;
    
    (match Z3.check_and_get_model ctx with
    | (Z3.L_FALSE,_) ->
        (* proved *)
        printf "valid\n";
        if not is_valid then exitf "unexpected result";
    | (Z3.L_UNDEF,m) ->
        (* Z3 failed to prove/disprove f. *)
        printf "unknown\n";
        (* m should be viewed as a potential counterexample. *)
        printf "potential counterexample:\n%s\n" (Z3.model_to_string ctx m);
        if is_valid then exitf "unexpected result";
    | (Z3.L_TRUE,m) ->
        (* disproved *)
        printf "invalid\n";
        (* the model returned by Z3 is a counterexample *)
        printf "counterexample:\n%s\n" (Z3.model_to_string ctx m);
        if is_valid then exitf "unexpected result";
    );
    (* restore context *)
    Z3.pop ctx 1;
  end;;

(**
   Assert the axiom: function f is injective in the i-th argument.
   
   The following axiom is asserted into the logical context:

   forall (x_1, ..., x_n) finv(f(x_1, ..., x_i, ..., x_n)) = x_i

   Where, {e finv } is a fresh function declaration.
*)
let assert_inj_axiom ctx f i = 
  begin
    let sz = Z3.get_domain_size ctx f in
    if i >= sz then exitf "failed to create inj axiom";
    
    (* declare the i-th inverse of f: finv *)
    let finv_domain = Z3.get_range ctx f in
    let finv_range  = Z3.get_domain ctx f i in
    let finv        = Z3.mk_fresh_func_decl ctx "inv" [|finv_domain|] finv_range in

    (* allocate temporary arrays *)
    (* fill types, names and xs *)
    let types       = Z3.get_domains ctx f in
    let names       = Array.init sz (Z3.mk_int_symbol ctx) in
    let xs          = Array.init sz (fun j->Z3.mk_bound ctx j (types.(j))) in

    (* create f(x_0, ..., x_i, ..., x_{n-1}) *)
    let fxs         = Z3.mk_app ctx f xs in

    (* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) *)
    let finv_fxs    = mk_unary_app ctx finv fxs in

    (* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i *)
    let eq          = Z3.mk_eq ctx finv_fxs (xs.(i)) in

    (* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier *)
    let p           = Z3.mk_pattern ctx [|fxs|] in
    printf "pattern: %s\n" (Z3.ast_to_string ctx (Z3.pattern_ast_to_ast ctx p));
    printf "\n";

    (* create & assert quantifier *)
    let q           = Z3.mk_forall ctx 
                                   0 (* using default weight *)
                                   [|p|] (* the "array" of patterns *)
                                   types
                                   names
                                   eq
    in
    printf "assert axiom:\n%s\n" (Z3.ast_to_string ctx q);
    Z3.assert_cnstr ctx q;
  end;;

(**
   Assert the axiom: function f is commutative. 
   
   This example uses the SMT-LIB parser to simplify the axiom construction.
*)
let assert_comm_axiom ctx f =
  begin
    let t      = Z3.get_range ctx f in
    if Z3.get_domain_size ctx f != 2 || not (equal_types ctx (Z3.get_domain ctx f 0) t) || not (equal_types ctx (Z3.get_domain ctx f 1) t) then 
      exitf "function must be binary, and argument types must be equal to return type";
    (* Inside the parser, function f will be referenced using the symbol 'f'. *)
    let f_name = Z3.mk_string_symbol ctx "f" in
    (* Inside the parser, type t will be referenced using the symbol 'T'. *)
    let t_name = Z3.mk_string_symbol ctx "T" in
    let str    = "(benchmark comm :formula (forall (x T) (y T) (= (f x y) (f y x))))" in
    let q = Z3.parse_smtlib_string_formula ctx str [|t_name|] [|t|] [|f_name|] [|f|] in
    printf "assert axiom:\n%s\n" (Z3.ast_to_string ctx q);
    Z3.assert_cnstr ctx q;
  end;;

(**
   Z3 does not support explicitly tuple updates. They can be easily implemented 
   as macros. The argument {e t } must have tuple type. 
   A tuple update is a new tuple where field {e i } has value {e new_val }, and all
   other fields have the value of the respective field of {e t }.

   {e update(t, i, new_val) } is equivalent to
   {e mk_tuple(proj_0(t), ..., new_val, ..., proj_n(t)) } 
*)
let mk_tuple_update c t i new_val =
  begin
    let ty = Z3.get_type c t in
    let (mk_tuple_decl,fields)=Z3.get_tuple_type c ty in
    if i>=Array.length fields then exitf "invalid tuple update, index is too big";
    let f j = 
      if i = j then (* use new_val at position i: *) new_val
      else (* use field j of t: *) (mk_unary_app c (fields.(j)) t)
    in let new_fields = Array.init (Array.length fields) f in
    Z3.mk_app c (Z3.get_tuple_type_mk_decl c ty) new_fields;
  end;;

(**
   Display a symbol in the given output stream.
*)
let display_symbol c out s =
  match Z3.symbol_refine c s with
  | Z3.Symbol_int i -> fprintf out "#%d" i;
  | Z3.Symbol_string r ->fprintf out "%s" r;
  | Z3.Symbol_unknown -> ();;

(**
   Display the given type.
*)
let rec display_type c out ty =
  begin
    match Z3.type_refine c ty with 
    | Z3.Type_uninterpreted s -> display_symbol c out s;
    | Z3.Type_bool -> fprintf out "bool";
    | Z3.Type_int -> fprintf out "int";
    | Z3.Type_real -> fprintf out "real";
    | Z3.Type_bv sz -> fprintf out "bv%d" sz;
    | Z3.Type_array (domain, range) ->
      fprintf out "[";
      display_type c out domain;
      fprintf out "->";
      display_type c out range;
      fprintf out "]";
    | Z3.Type_tuple (_, fields) ->
      fprintf out "(";
      let f i v = 
        if i>0 then fprintf out ", ";
        display_type c out (Z3.get_range c v);
      in Array.iteri f fields;
      fprintf out ")";
    | Z3.Type_unknown s ->
      fprintf out "unknown[";
      display_symbol c out s;
      fprintf out "unknown]";
  end;;

(**
   Custom value pretty printer. 

   This function demonstrates how to use the API to navigate values 
   found in Z3 models.
*)
let rec display_value c out v =
  begin
    match Z3.value_refine c v with
    | Z3.Value_bool bv -> fprintf out "%s" (if bv then "true" else "false");
    | Z3.Value_numeral (num_buffer,t) ->
      fprintf out "%s" num_buffer;
      fprintf out ":";
      display_type c out t;
    | Z3.Value_tuple fields ->
      fprintf out "[";
      let f i f=
        if i>0 then fprintf out ", ";
        display_value c out f;
      in
      Array.iteri f fields;
      fprintf out "]";
    | Z3.Value_array (domain_range_pairs,array_else) ->
      fprintf out "{";
      let f i (d,r)=
        if i>0 then fprintf out ", ";
        fprintf out "(";
        display_value c out d;
        fprintf out "|->";
        display_value c out r;
        fprintf out ")";
        if i=Array.length domain_range_pairs-1 then fprintf out ", ";
      in
      Array.iteri f domain_range_pairs;
      fprintf out "(else|->";
      display_value c out array_else;
      fprintf out ")}";
    | Z3.Value_unknown -> fprintf out "#unknown";
  end;;

(**
   Custom function interpretations pretty printer.
*)
let display_function_interpretations c out m =
  begin
    fprintf out "function interpretations:\n";
    let display_function (internal, name, entries, func_else) =
      if not internal then
      begin
        display_symbol c out name;
        fprintf out " = {";
        let display_entry j (args,valu) =
          if j > 0 then fprintf out ", ";
          fprintf out "(";
          let f k arg =
            if k > 0 then fprintf out ", ";
            display_value c out arg
          in Array.iteri f args;
          fprintf out "|->";
          display_value c out valu;
          fprintf out ")";
        in Array.iteri display_entry entries;
        if Array.length entries > 0 then fprintf out ", ";
        fprintf out "(else|->";
        display_value c out func_else;
        fprintf out ")}\n";
      end;
    in
    Array.iter display_function (Z3.get_model_funcs c m);
  end;;

(**
   Custom model pretty printer.
*)
let display_model c out m = 
  begin
    let constants=Z3.get_model_constants c m in
    let f i e =
      let name = Z3.get_decl_name c e in
      display_symbol c out name;
      fprintf out " = ";
      display_value c out (Z3.get_value c m e);
      fprintf out "\n"
    in Array.iteri f constants;
    display_function_interpretations c out m;
  end;;

(**
   Similar to #check, but uses #display_model instead of #Z3_model_to_string.
*)
let check2 ctx expected_result =
  begin
    let (result,m) = Z3.check_and_get_model ctx in
    (match result with
    | Z3.L_FALSE ->
      printf "unsat\n";
    | Z3.L_UNDEF ->
      printf "unknown\n";
      printf "potential model:\n";
      display_model ctx stdout m;
    | Z3.L_TRUE ->
      printf "sat\n";
      display_model ctx stdout m;
    );
    if result != expected_result then exitf "unexpected result";
  end;;

(**
   Display Z3 version in the standard output.
*)
let display_version() =
  begin
    let (major, minor, build, revision)=Z3.get_version() in
    printf "Z3 %d.%d.%d.%d\n" major minor build revision;
  end;;

(*
   @name Examples
*)

(**
   "Hello world" example: create a Z3 logical context, and delete it.
*)
let simple_example() =
  begin
    printf "\nsimple_example\n";
    let ctx = mk_context [||] in
    (* do something with the context *)
    printf "CONTEXT:\n%sEND OF CONTEXT\n" (Z3.context_to_string ctx);
    (* delete logical context *)
    Z3.del_context ctx;
  end;;

(**
  Demonstration of how Z3 can be used to prove validity of
  De Morgan's Duality Law: {e not(x and y) <-> (not x) or ( not y) }
*)
let demorgan() =
  begin
    printf "\nDeMorgan\n";
    let ctx = mk_context [||] in
    let bool_type = Z3.mk_bool_type ctx in
    let symbol_x = Z3.mk_int_symbol ctx 0 in
    let symbol_y = Z3.mk_int_symbol ctx 1 in
    let x = Z3.mk_const ctx symbol_x bool_type in
    let y = Z3.mk_const ctx symbol_y bool_type in
  
    (* De Morgan - with a negation around: *)  
    (* !(!(x && y) <-> (!x || !y)) *)
    let not_x = Z3.mk_not ctx x in
    let not_y = Z3.mk_not ctx y in
    let x_and_y = Z3.mk_and ctx [|x;y|] in
    let ls = Z3.mk_not ctx x_and_y in
    let rs = Z3.mk_or ctx [|not_x;not_y|] in
    let conjecture = Z3.mk_iff ctx ls rs in
    let negated_conjecture = Z3.mk_not ctx conjecture in

    Z3.assert_cnstr ctx negated_conjecture;
    (match Z3.check ctx with
    | Z3.L_FALSE ->
      (* The negated conjecture was unsatisfiable, hence the conjecture is valid *)
      printf "DeMorgan is valid\n"
    | Z3.L_UNDEF ->
      (* Check returned undef *)
      printf "Undef\n"
    | Z3.L_TRUE ->
      (* The negated conjecture was satisfiable, hence the conjecture is not valid *)
      Printf.printf "DeMorgan is not valid\n");
    Z3.del_context ctx;
  end;;

(**
   Find a model for {e x xor y }.
*)
let find_model_example1() =
  begin
    printf "\nfind_model_example1\n";
    let ctx     = mk_context [||] in
    let x       = mk_bool_var ctx "x" in
    let y       = mk_bool_var ctx "y" in
    let x_xor_y = Z3.mk_xor ctx x y in
    Z3.assert_cnstr ctx x_xor_y;
    printf "model for: x xor y\n";
    check ctx Z3.L_TRUE;
    Z3.del_context ctx;
  end;;

(**
   Find a model for {e x < y + 1, x > 2 }.
   Then, assert {e not(x = y) }, and find another model.
*)
let find_model_example2() =
  begin
    printf "\nfind_model_example2\n";
    let ctx        = mk_context [||] in
    let x          = mk_int_var ctx "x" in
    let y          = mk_int_var ctx "y" in
    let one        = mk_int ctx 1 in
    let two        = mk_int ctx 2 in
    let y_plus_one = Z3.mk_add ctx [|y;one|] in
    let c1         = Z3.mk_lt ctx x y_plus_one in
    let c2         = Z3.mk_gt ctx x two in
    Z3.assert_cnstr ctx c1;
    Z3.assert_cnstr ctx c2;
    printf "model for: x < y + 1, x > 2\n";
    check ctx Z3.L_TRUE;

    (* assert not(x = y) *)
    let x_eq_y     = Z3.mk_eq ctx x y in
    let c3         = Z3.mk_not ctx x_eq_y in
    Z3.assert_cnstr ctx c3;
    printf "model for: x < y + 1, x > 2, not(x = y)\n";
    check ctx Z3.L_TRUE;
    Z3.del_context ctx;
  end;;
(*
(**
   Prove {e x = y implies g(x) = g(y) }, and
   disprove {e x = y implies g(g(x)) = g(y) }.

   This function demonstrates how to create uninterpreted types and
   functions.
*)
let prove_example1() =
  begin
    printf "\nprove_example1\n";

    let ctx        = mk_context [||] in
    
    (* create uninterpreted type. *)
    let u_name     = Z3.mk_string_symbol ctx "U" in
    let u          = Z3.mk_uninterpreted_type ctx u_name in
    
    (* declare function g *)
    let g_name      = Z3.mk_string_symbol ctx "g" in
    let g           = Z3.mk_func_decl ctx g_name [|u|] u in

    (* create x and y *)
    let x_name      = Z3.mk_string_symbol ctx "x" in
    let y_name      = Z3.mk_string_symbol ctx "y" in
    let x           = Z3.mk_const ctx x_name u in
    let y           = Z3.mk_const ctx y_name u in
    (* create g(x), g(y) *)
    let gx          = mk_unary_app ctx g x in
    let gy          = mk_unary_app ctx g y in
    
    (* assert x = y *)
    let eq          = Z3.mk_eq ctx x y in
    Z3.assert_cnstr ctx eq;

    (* prove g(x) = g(y) *)
    let f           = Z3.mk_eq ctx gx gy in
    printf "prove: x = y implies g(x) = g(y)\n";
    prove ctx f true;

    (* create g(g(x)) *)
    let ggx         = mk_unary_app ctx g gx in
    
    (* disprove g(g(x)) = g(y) *)
    let f           = Z3.mk_eq ctx ggx gy in
    printf "disprove: x = y implies g(g(x)) = g(y)\n";
    prove ctx f false;

    Z3.del_context ctx;
  end;;

(**
   Prove {e not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0  }.
   Then, show that {e z < -1 } is not implied.

   This example demonstrates how to combine uninterpreted functions and arithmetic.
*)
let prove_example2() =
  begin
    printf "\nprove_example2\n";
    
    let ctx        = mk_context [||] in

    (* declare function g *)
    let int_type    = Z3.mk_int_type ctx in
    let g_name      = Z3.mk_string_symbol ctx "g" in
    let g           = Z3.mk_func_decl ctx g_name [|int_type|] int_type in

    (* create x, y, and z *)
    let x           = mk_int_var ctx "x" in
    let y           = mk_int_var ctx "y" in
    let z           = mk_int_var ctx "z" in

    (* create gx, gy, gz *)
    let gx          = mk_unary_app ctx g x in
    let gy          = mk_unary_app ctx g y in
    let gz          = mk_unary_app ctx g z in
    
    (* create zero *)
    let zero        = mk_int ctx 0 in

    (* assert not(g(g(x) - g(y)) = g(z)) *)
    let gx_gy       = Z3.mk_sub ctx [|gx;gy|] in
    let ggx_gy      = mk_unary_app ctx g gx_gy in
    let eq          = Z3.mk_eq ctx ggx_gy gz in
    let c1          = Z3.mk_not ctx eq in
    Z3.assert_cnstr ctx c1;

    (* assert x + z <= y *)
    let x_plus_z    = Z3.mk_add ctx [|x;z|] in
    let c2          = Z3.mk_le ctx x_plus_z y in
    Z3.assert_cnstr ctx c2;

    (* assert y <= x *)
    let c3          = Z3.mk_le ctx y x in
    Z3.assert_cnstr ctx c3;

    (* prove z < 0 *)
    let f           = Z3.mk_lt ctx z zero in
    printf "prove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0\n";
    prove ctx f true;

    (* disprove z < -1 *)
    let minus_one   = mk_int ctx (-1) in
    let f           = Z3.mk_lt ctx z minus_one in
    printf "disprove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < -1\n";
    prove ctx f false;

    Z3.del_context ctx;
  end;;

(**
   Show how push & pop can be used to create "backtracking"
   points.

   This example also demonstrates how big numbers can be created in Z3.
*)
let push_pop_example1() =
  begin
    printf "\npush_pop_example1\n";
    let ctx        = mk_context [||] in

    (* create a big number *)
    let int_type   = Z3.mk_int_type ctx in
    let big_number = Z3.mk_numeral ctx "1000000000000000000000000000000000000000000000000000000" int_type in
    
    (* create number 3 *)
    let three      = Z3.mk_numeral ctx "3" int_type in

    (* create x *)
    let x_sym      = Z3.mk_string_symbol ctx "x" in
    let x          = Z3.mk_const ctx x_sym int_type in

    (* assert x >= "big number" *)
    let c1         = Z3.mk_ge ctx x big_number in
    printf "assert: x >= 'big number'\n";
    Z3.assert_cnstr ctx c1;

    (* create a backtracking point *)
    printf "push\n";
    Z3.push ctx;

    (* assert x <= 3 *)
    let c2         = Z3.mk_le ctx x three in
    printf "assert: x <= 3\n";
    Z3.assert_cnstr ctx c2;

    (* context is inconsistent at this point *)
    check2 ctx Z3.L_FALSE;

    (* backtrack: the constraint x <= 3 will be removed, since it was
       asserted after the last push. *)
    printf "pop\n";
    Z3.pop ctx 1;

    (* the context is consistent again. *)
    check2 ctx Z3.L_TRUE;

    (* new constraints can be asserted... *)
    
    (* create y *)
    let y_sym      = Z3.mk_string_symbol ctx "y" in
    let y          = Z3.mk_const ctx y_sym int_type in

    (* assert y > x *)
    let c3         = Z3.mk_gt ctx y x in
    printf "assert: y > x\n";
    Z3.assert_cnstr ctx c3;

    (* the context is still consistent. *)
    check2 ctx Z3.L_TRUE;
    
    Z3.del_context ctx;
  end;;

(**
   Prove that {e f(x, y) = f(w, v) implies y = v } when 
   {e f } is injective in the second argument.
*)
let quantifier_example1() =
  begin
    printf "\nquantifier_example1\n";

    (* If quantified formulas are asserted in a logical context, then
       the model produced by Z3 should be viewed as a potential model.

       The option PARTIAL_MODELS=true will allow Z3 to create partial
       function interpretations, that is, the "else" part is
       unspecified.
    *)
    let ctx = mk_context [|("PARTIAL_MODELS","true")|] in

    (* declare function f *)
    let int_type    = Z3.mk_int_type ctx in
    let f_name      = Z3.mk_string_symbol ctx "f" in
    let f           = Z3.mk_func_decl ctx f_name [|int_type; int_type|] int_type in
  
    (* assert that f is injective in the second argument. *)
    assert_inj_axiom ctx f 1;
    
    (* create x, y, v, w, fxy, fwv *)
    let x           = mk_int_var ctx "x" in
    let y           = mk_int_var ctx "y" in
    let v           = mk_int_var ctx "v" in
    let w           = mk_int_var ctx "w" in
    let fxy         = mk_binary_app ctx f x y in
    let fwv         = mk_binary_app ctx f w v in
    
    (* assert f(x, y) = f(w, v) *)
    let p1          = Z3.mk_eq ctx fxy fwv in
    Z3.assert_cnstr ctx p1;

    (* prove f(x, y) = f(w, v) implies y = v *)
    let p2          = Z3.mk_eq ctx y v in
    printf "prove: f(x, y) = f(w, v) implies y = v\n";
    prove ctx p2 true;

    (* disprove f(x, y) = f(w, v) implies x = w *)
    (* using check2 instead of prove *)
    let p3          = Z3.mk_eq ctx x w in
    let not_p3      = Z3.mk_not ctx p3 in
    Z3.assert_cnstr ctx not_p3;
    printf "disprove: f(x, y) = f(w, v) implies x = w\n";
    printf "that is: not(f(x, y) = f(w, v) implies x = w) is satisfiable\n";
    check2 ctx Z3.L_TRUE;

    Z3.del_context ctx;
  end;;

(**
   Prove {e store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3)) }.
   
   This example demonstrates how to use the array theory.
*)
let array_example1() =
  begin
    printf "\narray_example1\n";

    let ctx = mk_context [||] in

    let int_type    = Z3.mk_int_type ctx in
    let array_type  = Z3.mk_array_type ctx int_type int_type in

    let a1          = mk_var ctx "a1" array_type in
    let a2          = mk_var ctx "a2" array_type in
    let i1          = mk_var ctx "i1" int_type in
    let i2          = mk_var ctx "i2" int_type in
    let i3          = mk_var ctx "i3" int_type in
    let v1          = mk_var ctx "v1" int_type in
    let v2          = mk_var ctx "v2" int_type in
    
    let st1         = Z3.mk_store ctx a1 i1 v1 in
    let st2         = Z3.mk_store ctx a2 i2 v2 in
    
    let sel1        = Z3.mk_select ctx a1 i3 in
    let sel2        = Z3.mk_select ctx a2 i3 in

    (* create antecedent *)
    let antecedent  = Z3.mk_eq ctx st1 st2 in

    (* create consequent: i1 = i3 or  i2 = i3 or select(a1, i3) = select(a2, i3) *)
    let ds = [|
        Z3.mk_eq ctx i1 i3;
        Z3.mk_eq ctx i2 i3;
        Z3.mk_eq ctx sel1 sel2;
      |] in

    let consequent  = Z3.mk_or ctx ds in

    (* prove store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3)) *)
    let thm         = Z3.mk_implies ctx antecedent consequent in
    printf "prove: store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))\n";
    printf "%s\n" (Z3.ast_to_string ctx thm);
    prove ctx thm true;

    Z3.del_context ctx;
  end;;

(**
   Show that {e distinct(a_0, ... , a_n) } is
   unsatisfiable when {e a_i's } are arrays from boolean to
   boolean and n > 4.

   This example also shows how to use the {e distinct } construct.
*)
let array_example2() =
  begin
    printf "\narray_example2\n";

    for n = 2 to 5 do
      printf "n = %d\n" n;
      let ctx = mk_context [||] in
      
      let bool_type   = Z3.mk_bool_type ctx in
      let array_type  = Z3.mk_array_type ctx bool_type bool_type in
      
      (* create arrays *)
      let a = Array.init n
        (fun i->Z3.mk_const ctx (Z3.mk_int_symbol ctx i) array_type) in
      
      (* assert distinct(a[0], ..., a[n]) *)
      let d = Z3.mk_distinct ctx a in
      printf "%s\n" (Z3.ast_to_string ctx d);
      Z3.assert_cnstr ctx d;

      (* context is satisfiable if n < 5 *)
      check2 ctx (if n < 5 then Z3.L_TRUE else Z3.L_FALSE);

      Z3.del_context ctx;
    done
  end;;

(**
   Simple array type construction/deconstruction example.
*)
let array_example3() =
  begin
    printf "\narray_example3\n";

    let ctx      = mk_context [||] in

    let bool_type  = Z3.mk_bool_type ctx in
    let int_type   = Z3.mk_int_type ctx in
    let array_type = Z3.mk_array_type ctx int_type bool_type in

    let (domain,range) = Z3.get_array_type ctx array_type in
    printf "domain: ";
    display_type ctx stdout domain;
    printf "\n";
    printf "range:  ";
    display_type ctx stdout range;
    printf "\n";

    if (not (Z3.is_eq ctx (Z3.type_ast_to_ast ctx int_type)  
                          (Z3.type_ast_to_ast ctx domain))) ||
       (not (Z3.is_eq ctx (Z3.type_ast_to_ast ctx bool_type)
                          (Z3.type_ast_to_ast ctx range))) then
        exitf "invalid array type";
    Z3.del_context ctx;
  end;;

(**
   Simple tuple type example. It creates a tuple that is a pair of real numbers.
*)
let tuple_example1() =
  begin
    printf "\ntuple_example1\n";
    
    let ctx       = mk_context [||] in

    let real_type = Z3.mk_real_type ctx in

    (* Create pair (tuple) type *)
    let mk_tuple_name = Z3.mk_string_symbol ctx "mk_pair" in
    let proj_names_0 = Z3.mk_string_symbol ctx "get_x" in
    let proj_names_1 = Z3.mk_string_symbol ctx "get_y" in
    let proj_names = [|proj_names_0; proj_names_1|] in
    let proj_types = [|real_type;real_type|] in
    (* Z3_mk_tuple_type will set mk_tuple_decl and proj_decls *)
    let (pair_type,mk_tuple_decl,proj_decls) = Z3.mk_tuple_type ctx mk_tuple_name proj_names proj_types in
    let get_x_decl    = proj_decls.(0) in (* function that extracts the first element of a tuple. *)
    let get_y_decl    = proj_decls.(1) in (* function that extracts the second element of a tuple. *)

    printf "tuple_type: ";
    display_type ctx stdout pair_type;
    printf "\n";

    begin
      (* prove that get_x(mk_pair(x,y)) == 1 implies x = 1*)
      let x    = mk_real_var ctx "x" in
      let y    = mk_real_var ctx "y" in
      let app1 = mk_binary_app ctx mk_tuple_decl x y in
      let app2 = mk_unary_app ctx get_x_decl app1 in 
      let one  = Z3.mk_numeral ctx "1" real_type in
      let eq1  = Z3.mk_eq ctx app2 one in
      let eq2  = Z3.mk_eq ctx x one in
      let thm  = Z3.mk_implies ctx eq1 eq2 in
      printf "prove: get_x(mk_pair(x, y)) = 1 implies x = 1\n";
      prove ctx thm true;

      (* disprove that get_x(mk_pair(x,y)) == 1 implies y = 1*)
      let eq3  = Z3.mk_eq ctx y one in
      let thm  = Z3.mk_implies ctx eq1 eq3 in
      printf "disprove: get_x(mk_pair(x, y)) = 1 implies y = 1\n";
      prove ctx thm false;
    end;

    begin
      (* prove that get_x(p1) = get_x(p2) and get_y(p1) = get_y(p2) implies p1 = p2 *)
      let p1          = mk_var ctx "p1" pair_type in
      let p2          = mk_var ctx "p2" pair_type in
      let x1          = mk_unary_app ctx get_x_decl p1 in
      let y1          = mk_unary_app ctx get_y_decl p1 in
      let x2          = mk_unary_app ctx get_x_decl p2 in
      let y2          = mk_unary_app ctx get_y_decl p2 in
      let antecedents_0 = Z3.mk_eq ctx x1 x2 in
      let antecedents_1 = Z3.mk_eq ctx y1 y2 in
      let antecedents = [|antecedents_0; antecedents_1|] in
      let antecedent  = Z3.mk_and ctx antecedents in
      let consequent  = Z3.mk_eq ctx p1 p2 in
      let thm         = Z3.mk_implies ctx antecedent consequent in
      printf "prove: get_x(p1) = get_x(p2) and get_y(p1) = get_y(p2) implies p1 = p2\n";
      prove ctx thm true;

      (* disprove that get_x(p1) = get_x(p2) implies p1 = p2 *)
      let thm         = Z3.mk_implies ctx (antecedents.(0)) consequent in
      printf "disprove: get_x(p1) = get_x(p2) implies p1 = p2\n";
      prove ctx thm false;
    end;

    begin
      (* demonstrate how to use the mk_tuple_update function *)
      (* prove that p2 = update(p1, 0, 10) implies get_x(p2) = 10 *)
      let p1             = mk_var ctx "p1" pair_type in
      let p2             = mk_var ctx "p2" pair_type in
      let one            = Z3.mk_numeral ctx "1" real_type in
      let ten            = Z3.mk_numeral ctx "10" real_type in
      let updt           = mk_tuple_update ctx p1 0 ten in
      let antecedent     = Z3.mk_eq ctx p2 updt in
      let x              = mk_unary_app ctx get_x_decl p2 in
      let consequent     = Z3.mk_eq ctx x ten in
      let thm            = Z3.mk_implies ctx antecedent consequent in
      printf "prove: p2 = update(p1, 0, 10) implies get_x(p2) = 10\n";
      prove ctx thm true;

      (* disprove that p2 = update(p1, 0, 10) implies get_y(p2) = 10 *)
      let y              = mk_unary_app ctx get_y_decl p2 in
      let consequent     = Z3.mk_eq ctx y ten in
      let thm            = Z3.mk_implies ctx antecedent consequent in
      printf "disprove: p2 = update(p1, 0, 10) implies get_y(p2) = 10\n";
      prove ctx thm false;
    end;

    Z3.del_context ctx;
  end;;

(**
   Simple bit-vector example. This example disproves that x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers
 *)
let bitvector_example1() =
  begin
    printf "\nbitvector_example1\n";
    
    let ctx       = mk_context [||] in
    
    let bv_type   = Z3.mk_bv_type ctx 32 in
    
    let x           = mk_var ctx "x" bv_type in
    let zero        = Z3.mk_numeral ctx "0" bv_type in
    let ten         = Z3.mk_numeral ctx "10" bv_type in
    let x_minus_ten = Z3.mk_bvsub ctx x ten in
    (* bvsle is signed less than or equal to *)
    let c1          = Z3.mk_bvsle ctx x ten in
    let c2          = Z3.mk_bvsle ctx x_minus_ten zero in
    let thm         = Z3.mk_iff ctx c1 c2 in
    printf "disprove: x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers\n";
    prove ctx thm false;
    
    Z3.del_context ctx;
  end;;

(**
   Find x and y such that: x ^ y - 103 == x * y
 *)
let bitvector_example2() =
  begin
    printf "\nbitvector_example2\n";
    let ctx       = mk_context [||] in
    (* construct x ^ y - 103 == x * y *)
    let bv_type   = Z3.mk_bv_type ctx 32 in
    let x         = mk_var ctx "x" bv_type in
    let y         = mk_var ctx "y" bv_type in
    let x_xor_y   = Z3.mk_bvxor ctx x y in
    let c103      = Z3.mk_numeral ctx "103" bv_type in
    let lhs       = Z3.mk_bvsub ctx x_xor_y c103 in
    let rhs       = Z3.mk_bvmul ctx x y in
    let ctr       = Z3.mk_eq ctx lhs rhs in
    printf "find values of x and y, such that x ^ y - 103 == x * y\n";
    Z3.assert_cnstr ctx ctr;
    check ctx Z3.L_TRUE;
    Z3.del_context ctx;
  end;;

(**
   Demonstrate how to use #Z3_eval.
*)
let eval_example1() =
  begin
    printf "\neval_example1\n";
    
    let ctx        = mk_context [||] in
    let x          = mk_int_var ctx "x" in
    let y          = mk_int_var ctx "y" in
    let two        = mk_int ctx 2 in
    
    (* assert x < y *)
    let c1         = Z3.mk_lt ctx x y in
    Z3.assert_cnstr ctx c1;

    (* assert x > 2 *)
    let c2         = Z3.mk_gt ctx x two in
    Z3.assert_cnstr ctx c2;

    (* find model for the constraints above *)
    match Z3.check_and_get_model ctx with
    | (Z3.L_TRUE, m) ->
      begin
        let args = [|x; y|] in
        printf "MODEL:\n%s" (Z3.model_to_string ctx m);
        let x_plus_y = Z3.mk_add ctx args in
        printf "\nevaluating x+y\n";
        (match Z3.eval ctx m x_plus_y with
        | (true,v) ->
          printf "result = ";
          display_value ctx stdout v;
          printf "\n";
        | _ -> 
          exitf "failed to evaluate: x+y";
        );
      end;
    | _ ->
      exitf "the constraints are satisfiable";

    Z3.del_context ctx;
  end;;

(**
   Several logical context can be used simultaneously.
*)
let two_contexts_example1() =
  begin
    printf "\ntwo_contexts_example1\n";
    (* using the same (default) configuration to initialized both logical contexts. *)
    let ctx1 = mk_context [||] in
    let ctx2 = mk_context [||] in
    let x1 = Z3.mk_const ctx1 (Z3.mk_int_symbol ctx1 0) (Z3.mk_bool_type ctx1) in
    let x2 = Z3.mk_const ctx2 (Z3.mk_int_symbol ctx2 0) (Z3.mk_bool_type ctx2) in
    Z3.del_context ctx1;
    (* ctx2 can still be used. *)
    printf "%s\n" (Z3.ast_to_string ctx2 x2);
    Z3.del_context ctx2;
  end;;

(**
   Demonstrates how error codes can be read insted of registering an error handler.
 *)
let error_code_example1() =
  begin
    printf "\nerror_code_example1\n";
    
    let ctx        = mk_context [||] in
    let x          = mk_bool_var ctx "x" in
    let x_decl     = Z3.get_const_ast_decl ctx (Z3.to_const_ast ctx x) in
    Z3.assert_cnstr ctx x;
    
    match Z3.check_and_get_model ctx with
    | (Z3.L_TRUE,m) ->
      begin
        let v = Z3.get_value ctx  m x_decl in
        printf "last call succeeded.\n";

        (* The following call will fail since the value of x is a boolean *)
        (try ignore(Z3.get_numeral_value_string ctx v)
        with | _ -> printf "last call failed.\n");

        Z3.del_context ctx;
      end
    | _ -> exitf "unexpected result";
  end;;

(**
   Demonstrates how Z3 exceptions can be used.
*)
let error_code_example2() =
  begin
    printf "\nerror_code_example2\n";

    let ctx   = mk_context [||] in
    try
      let x   = mk_int_var ctx "x" in
      let y   = mk_bool_var ctx "y" in
      printf "before Z3_mk_iff\n";
      let app = Z3.mk_iff ctx x y in
      printf "unreachable";
    with | _ -> printf "Z3 error: type error.\n";
    Z3.del_context ctx;
  end;;

(**
   Demonstrates how to use the SMTLIB parser.
 *)
let parser_example1() =
  begin
    printf "\nparser_example1\n";
    
    let ctx          = mk_context [||] in
    let str          = "(benchmark tst :extrafuns ((x Int) (y Int)) :formula (> x y) :formula (> x 0))" in
    Z3.enable_arithmetic(ctx);
    let (formulas,_,_) = Z3.parse_smtlib_string_x ctx str [||] [||] [||] [||] in
    let f i c        =
      printf "formula %d: %s\n" i (Z3.ast_to_string ctx c);
      Z3.assert_cnstr ctx c;
    in Array.iteri f formulas;
    check ctx Z3.L_TRUE;
    Z3.del_context ctx;
  end;;

(**
   Demonstrates how to initialize the parser symbol table.
 *)
let parser_example2() =
  begin
    printf "\nparser_example2\n";
    
    let ctx          = mk_context [||] in
    let x            = mk_int_var ctx "x" in
    let x_decl       = Z3.get_const_ast_decl ctx (Z3.to_const_ast ctx x) in
    let y            = mk_int_var ctx "y" in
    let y_decl       = Z3.get_const_ast_decl ctx (Z3.to_const_ast ctx y) in
    let decls        = [| x_decl; y_decl |] in
    let a            = Z3.mk_string_symbol ctx "a" in
    let b            = Z3.mk_string_symbol ctx "b" in
    let names        = [| a; b |] in
    let str          = "(benchmark tst :formula (> a b))" in
    let f  = Z3.parse_smtlib_string_formula ctx str [||] [||] names decls in
    printf "formula: %s\n" (Z3.ast_to_string ctx f);
    Z3.assert_cnstr ctx f;
    check ctx Z3.L_TRUE;
    Z3.del_context ctx;
  end;;

(**
   Demonstrates how to initialize the parser symbol table.
 *)
let parser_example3() =
  begin
    printf "\nparser_example3\n";
    
    let ctx      = mk_context [|("PARTIAL_MODELS","true")|] in
    let int_type = Z3.mk_int_type ctx in
    let g_name   = Z3.mk_string_symbol ctx "g" in
    let g        = Z3.mk_func_decl ctx g_name [| int_type; int_type |] int_type in
    let str      = "(benchmark tst :formula (forall (x Int) (y Int) (implies (= x y) (= (g x 0) (g 0 y)))))" in
    assert_comm_axiom ctx g;
    let thm = Z3.parse_smtlib_string_formula ctx str [||] [||] [|g_name|] [|g|] in
    printf "formula: %s\n" (Z3.ast_to_string ctx thm);
    prove ctx thm true;
    Z3.del_context ctx;
  end;;

(**
   Display the declarations, assumptions and formulas in a SMT-LIB string.
 *)
let parser_example4() =
  begin
    printf "\nparser_example4\n";
    
    let ctx          = mk_context [||] in
    let str          = "(benchmark tst :extrafuns ((x Int) (y Int)) :assumption (= x 20) :formula (> x y) :formula (> x 0))" in
    (* arithmetic theory is automatically initialized, when an
       int/real variable or arith operation is created using the API.
       Since no such function is invoked in this example, we should do
       that manually.
     *)
    Z3.enable_arithmetic ctx;
    let (formulas, assumptions, decls) = Z3.parse_smtlib_string_x ctx str [||] [||] [||] [||] in
    let f prefix i n = printf "%s %d: %s\n" prefix i (Z3.ast_to_string ctx n) in
    Array.iteri (f "declaration") (Array.map (Z3.const_decl_ast_to_ast ctx) decls);
    Array.iteri (f "assumption") assumptions;
    Array.iteri (f "formula") formulas;
    Z3.del_context ctx;
  end;;

(**
   Demonstrates how to handle parser errors using Z3 exceptions.
 *)
let parser_example5() =
  begin
    printf "\nparser_example5\n";
    let ctx = mk_context [||] in
    try 
      (* the following string has a parsing error: missing parenthesis *)
      let str = "(benchmark tst :extrafuns ((x Int (y Int)) :formula (> x y) :formula (> x 0))" in
      Z3.enable_arithmetic ctx;
      ignore(Z3.parse_smtlib_string_x ctx str [||] [||] [||] [||]);
    with | _ -> printf "Z3 error: parser error.\n";
    Z3.del_context ctx;    
  end;;

(**
   Demonstrates how to create if-then-else expressions.
 *)
let ite_example() =
  begin
    printf "\nite_example\n";
    let ctx         = mk_context [||] in
    let f           = Z3.mk_false ctx in
    let one         = mk_int ctx 1 in
    let zero        = mk_int ctx 0 in
    let ite         = Z3.mk_ite ctx f one zero in
    printf "term: %s\n" (Z3.ast_to_string ctx ite);
    Z3.del_context ctx;
  end;;

(**
   Demonstrates how to call the simplifier.
 *)
let simplifier_example() = 
  begin
    printf "\nsimplifier_example\n";
    let ctx = mk_context [||] in
    let x = mk_int_var ctx "x" in
    let y = mk_int_var ctx "y" in
    let z = mk_int_var ctx "z" in
    let t1 = Z3.mk_add ctx [| x; Z3.mk_sub ctx [| y; Z3.mk_add ctx [| x; z |] |] |] in
    let t2 = Z3.simplify ctx t1 in
    printf "%s -> %s\n" (Z3.ast_to_string ctx t1) (Z3.ast_to_string ctx t2);
    Z3.del_context ctx
  end;;

(**
   Demonstrates how to traverse a term by printing it in a funny way.
 *)
let rec print_term ctx bound_vars t = 
  match Z3.term_refine ctx t with
  | Z3.Term_app(k, f, args) ->
      printf "(";
      (match k with 
      | Z3.OP_ADD -> printf "'+'"
      | Z3.OP_SUB -> printf "'-'"
      | Z3.OP_MUL -> printf "'*'"
      | _ ->
	  let f' = Z3.const_decl_ast_to_ast ctx f in
	  printf "%s" (Z3.ast_to_string ctx f')
      );
      printf " ";
      Array.iter (print_term ctx bound_vars) args;
      printf ")";
  | Z3.Term_quantifier(binder, weight, patterns, bound, body) ->
      let bound_vars = bound::bound_vars in
      let print_pats terms = 
	printf "(";
	Array.iter (fun t -> print_term ctx bound_vars t; printf " ") terms;
	printf ")"
      in
      let print_bound (name,ty) = 
	let ty' = Z3.type_ast_to_ast ctx ty in
	printf "(";
	display_symbol ctx stdout name;
	printf " %s" (Z3.ast_to_string ctx ty');
	printf ") "
      in
      printf "(";
      (match binder with
      | Z3.Forall -> printf "Forall"
      | Z3.Exists -> printf "Exists");
      printf " ";
      Array.iter print_bound bound;
      Array.iter print_pats patterns;
      print_term ctx bound_vars body;
      printf ")"
  | Z3.Term_var(n,ty) -> 
      let rec pp_var bound_vars n = 
	match bound_vars with
	| [] -> assert false
	| bound::bound_vars -> 
	    let len = Array.length bound in
	    if n < len then
	      let (name, _) = bound.(len-n-1) in
	      begin
		display_symbol ctx stdout name;
		printf " "
	      end
	    else
	      pp_var bound_vars (n - len)
      in
      pp_var bound_vars n
  | Z3.Term_numeral(Z3.Numeral_large(s),ty) -> 
      printf "%s" s
  | Z3.Term_numeral(Z3.Numeral_small(num,den),ty) -> 
      printf "%s/%s" (Int64.to_string num) (Int64.to_string den)

(**
   Demonstrates term traversal.
*)

let traverse_term_example() = 
  let ctx = mk_context [||] in
  let f_name = Z3.mk_string_symbol ctx "f" in
  let int_type    = Z3.mk_int_type ctx in
  let f = Z3.mk_func_decl ctx f_name [| int_type |] int_type in
  let x = Z3.mk_bound ctx 1 int_type in
  let y = Z3.mk_bound ctx 0 int_type in
  let fx = Z3.mk_app ctx f [| x |] in
  let fy = Z3.mk_app ctx f [| y |] in
  let p = Z3.mk_pattern ctx [| fx ; fy |] in
  let types = [| int_type; int_type |] in
  let names = [| Z3.mk_string_symbol ctx "x"; Z3.mk_string_symbol ctx "y"|] in
  let body = Z3.mk_eq ctx fx (Z3.mk_add ctx [|fx; fy|]) in
  let q = Z3.mk_forall ctx 0 [|p|] types names body in
  printf "\ntraverse_term example\n";
  printf "%s\n" (Z3.ast_to_string ctx q);
  print_term ctx [] q;
  printf "\n";
  Z3.del_context ctx
*)


(**********************************************************************)
(****************** Axioms for Sets and Related Tests *****************)
(**********************************************************************)

let set_ax_str  = 
  "(benchmark sets
        :formula (forall (a S) (b S) 
		        (iff (seq a b) (forall (x E) (iff (elt x a) (elt x b)))))
        :formula (forall (x E) 
		        (not (elt x emp)))
        :formula (forall (x E) (a S) (b S) 
		        (iff (elt x (cup a b)) (or  (elt x a) (elt x b))))
        :formula (forall (x E) (a S) (b S) 
		        (iff (elt x (cap a b)) (and (elt x a) (elt x b))))
        :formula (forall (x E) (y E) 
		        (iff (elt x (sng y)) (= x y)) :pats {(elt x (sng y))} ))"

let set_q_str  =
"(benchmark setqs        
        :extrafuns  ((a1 S) (a2 S) (x1 E))
        :formula (seq emp emp)
        :formula (seq a1 a1)
        :formula (seq (cap a1 a2) (cap a2 a1))
        :formula (seq (cup a1 a2) (cup a2 a1))
        :formula (seq (cup a1 emp) a1)
        :formula (seq (cap a1 emp) emp)
        :formula (seq (cap a1 a1) a1)
        :formula (seq (cup a1 a1) a1)
        :formula (implies (seq a1 a2) (seq (cup a1 a2) a1))
        :formula (implies (seq a1 a2) (seq (cap a1 a2) a1))
        :formula (implies (elt x1 a1) (seq (cup (sng x1) a1) a1))
        :formula (implies (seq a1 a2) (seq (cup (sng x1) a1) (cup (sng x1) a2)))
        
        :formula (seq emp a1)
        :formula (seq (cup a1 a2) a1)
        :formula (seq (cap a1 a2) a1)
        :formula (seq (cup (sng x1) a1) a1))"

let rec mk_list n xs = 
  if n < 0 then xs else mk_list (n-1) (n::xs)

let sets_define_unint_type ctx s = 
  let t_s    = Z3.mk_string_symbol ctx s in
  let t_t    = Z3.mk_uninterpreted_type ctx t_s in
  (t_s, t_t)

let sets_define_op ctx s in_t_a out_t = 
  let f_s       = Z3.mk_string_symbol ctx s in
  let f_f       = Z3.mk_func_decl ctx f_s in_t_a out_t in
  (f_s, f_f)

let sets_prove ctx f = 
  begin
    Z3.push ctx;
    Z3.assert_cnstr ctx (Z3.mk_not ctx f) ;
    let out = 
      match Z3.check_and_get_model ctx with
      | (Z3.L_FALSE,_) -> "valid" 
      | (Z3.L_UNDEF,m) -> "unknown"
      | (Z3.L_TRUE,m)  -> "invalid" in
    printf "check: %s : %s \n" (Z3.ast_to_string ctx f) out;
    Z3.pop ctx 1
  end

let sets_setup () =
  let ctx               = mk_context [|("PARTIAL_MODELS","true")|] in
  let bool_t            = Z3.mk_bool_type ctx in
  let (elem_s,elem_t)   = sets_define_unint_type ctx "E" in
  let (set_s, set_t)    = sets_define_unint_type ctx "S" in 
  let (elt_s, elt_f)    = sets_define_op ctx "elt" [|elem_t; set_t|] bool_t in
  let (seq_s, seq_f)    = sets_define_op ctx "seq" [|set_t;  set_t|] bool_t in
  let (cap_s, cap_f)    = sets_define_op ctx "cap" [|set_t;  set_t|] set_t in
  let (cup_s, cup_f)    = sets_define_op ctx "cup" [|set_t;  set_t|] set_t in
  let (sng_s, sng_f)    = sets_define_op ctx "sng" [|elem_t|]        set_t in
  let (emp_s, emp_f)    = sets_define_op ctx "emp" [| |]             set_t in
  let t_n_a             = [|elem_s; set_s|] in
  let t_a               = [|elem_t; set_t|] in
  let f_n_a             = [|elt_s; seq_s; cap_s; cup_s; sng_s; emp_s|] in
  let f_a               = [|elt_f; seq_f; cap_f; cup_f; sng_f; emp_f|] in
  let axs               = 
    Z3.parse_smtlib_string ctx set_ax_str t_n_a t_a f_n_a f_a;
    List.map (Z3.get_smtlib_formula ctx) (mk_list 4 []) in
  let _                 = 
    List.iter (fun q -> 
                 printf "assert axiom:\n%s\n" (Z3.ast_to_string ctx q);
                 Z3.assert_cnstr ctx q) axs in
  let qs                =
    Z3.parse_smtlib_string ctx set_q_str t_n_a t_a f_n_a f_a;
    List.map (Z3.get_smtlib_formula ctx) (mk_list 15 []) in
  List.iter (sets_prove ctx) qs


(**********************************************************************)

let main() =
  begin
    display_version();
    sets_setup ();
    (*
    simple_example();
    demorgan();
    find_model_example1();
    find_model_example2();
    prove_example1();
    prove_example2();
    push_pop_example1();
    quantifier_example1();
    array_example1();
    array_example2();
    array_example3();
    tuple_example1();
    bitvector_example1();
    bitvector_example2();
    eval_example1();
    two_contexts_example1();
    error_code_example1();
    error_code_example2();
    parser_example1();
    parser_example2();
    parser_example4();
    parser_example5();
    ite_example();
    simplifier_example();
    traverse_term_example()*)
  end;;

let _ = main();;
