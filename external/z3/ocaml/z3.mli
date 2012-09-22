(* File generated from z3.idl *)

type config
and context
and sort
and func_decl
and ast
and app
and pattern
and symbol
and parameter
and model
and literals
and constructor
and constructor_list
and theory
and theory_data
and enum_1 =
  | L_FALSE
  | L_UNDEF
  | L_TRUE
and lbool = enum_1
and enum_2 =
  | INT_SYMBOL
  | STRING_SYMBOL
and symbol_kind = enum_2
and enum_3 =
  | PARAMETER_INT
  | PARAMETER_DOUBLE
  | PARAMETER_RATIONAL
  | PARAMETER_SYMBOL
  | PARAMETER_SORT
  | PARAMETER_AST
  | PARAMETER_FUNC_DECL
and parameter_kind = enum_3
and enum_4 =
  | UNINTERPRETED_SORT
  | BOOL_SORT
  | INT_SORT
  | REAL_SORT
  | BV_SORT
  | ARRAY_SORT
  | DATATYPE_SORT
  | RELATION_SORT
  | FINITE_DOMAIN_SORT
  | UNKNOWN_SORT
and sort_kind = enum_4
and enum_5 =
  | NUMERAL_AST
  | APP_AST
  | VAR_AST
  | QUANTIFIER_AST
  | UNKNOWN_AST
and ast_kind = enum_5
and enum_6 =
  | OP_TRUE
  | OP_FALSE
  | OP_EQ
  | OP_DISTINCT
  | OP_ITE
  | OP_AND
  | OP_OR
  | OP_IFF
  | OP_XOR
  | OP_NOT
  | OP_IMPLIES
  | OP_OEQ
  | OP_ANUM
  | OP_LE
  | OP_GE
  | OP_LT
  | OP_GT
  | OP_ADD
  | OP_SUB
  | OP_UMINUS
  | OP_MUL
  | OP_DIV
  | OP_IDIV
  | OP_REM
  | OP_MOD
  | OP_TO_REAL
  | OP_TO_INT
  | OP_IS_INT
  | OP_STORE
  | OP_SELECT
  | OP_CONST_ARRAY
  | OP_ARRAY_MAP
  | OP_ARRAY_DEFAULT
  | OP_SET_UNION
  | OP_SET_INTERSECT
  | OP_SET_DIFFERENCE
  | OP_SET_COMPLEMENT
  | OP_SET_SUBSET
  | OP_AS_ARRAY
  | OP_BNUM
  | OP_BIT1
  | OP_BIT0
  | OP_BNEG
  | OP_BADD
  | OP_BSUB
  | OP_BMUL
  | OP_BSDIV
  | OP_BUDIV
  | OP_BSREM
  | OP_BUREM
  | OP_BSMOD
  | OP_BSDIV0
  | OP_BUDIV0
  | OP_BSREM0
  | OP_BUREM0
  | OP_BSMOD0
  | OP_ULEQ
  | OP_SLEQ
  | OP_UGEQ
  | OP_SGEQ
  | OP_ULT
  | OP_SLT
  | OP_UGT
  | OP_SGT
  | OP_BAND
  | OP_BOR
  | OP_BNOT
  | OP_BXOR
  | OP_BNAND
  | OP_BNOR
  | OP_BXNOR
  | OP_CONCAT
  | OP_SIGN_EXT
  | OP_ZERO_EXT
  | OP_EXTRACT
  | OP_REPEAT
  | OP_BREDOR
  | OP_BREDAND
  | OP_BCOMP
  | OP_BSHL
  | OP_BLSHR
  | OP_BASHR
  | OP_ROTATE_LEFT
  | OP_ROTATE_RIGHT
  | OP_EXT_ROTATE_LEFT
  | OP_EXT_ROTATE_RIGHT
  | OP_INT2BV
  | OP_BV2INT
  | OP_CARRY
  | OP_XOR3
  | OP_PR_UNDEF
  | OP_PR_TRUE
  | OP_PR_ASSERTED
  | OP_PR_GOAL
  | OP_PR_MODUS_PONENS
  | OP_PR_REFLEXIVITY
  | OP_PR_SYMMETRY
  | OP_PR_TRANSITIVITY
  | OP_PR_TRANSITIVITY_STAR
  | OP_PR_MONOTONICITY
  | OP_PR_QUANT_INTRO
  | OP_PR_DISTRIBUTIVITY
  | OP_PR_AND_ELIM
  | OP_PR_NOT_OR_ELIM
  | OP_PR_REWRITE
  | OP_PR_REWRITE_STAR
  | OP_PR_PULL_QUANT
  | OP_PR_PULL_QUANT_STAR
  | OP_PR_PUSH_QUANT
  | OP_PR_ELIM_UNUSED_VARS
  | OP_PR_DER
  | OP_PR_QUANT_INST
  | OP_PR_HYPOTHESIS
  | OP_PR_LEMMA
  | OP_PR_UNIT_RESOLUTION
  | OP_PR_IFF_TRUE
  | OP_PR_IFF_FALSE
  | OP_PR_COMMUTATIVITY
  | OP_PR_DEF_AXIOM
  | OP_PR_DEF_INTRO
  | OP_PR_APPLY_DEF
  | OP_PR_IFF_OEQ
  | OP_PR_NNF_POS
  | OP_PR_NNF_NEG
  | OP_PR_NNF_STAR
  | OP_PR_CNF_STAR
  | OP_PR_SKOLEMIZE
  | OP_PR_MODUS_PONENS_OEQ
  | OP_PR_TH_LEMMA
  | OP_RA_STORE
  | OP_RA_EMPTY
  | OP_RA_IS_EMPTY
  | OP_RA_JOIN
  | OP_RA_UNION
  | OP_RA_WIDEN
  | OP_RA_PROJECT
  | OP_RA_FILTER
  | OP_RA_NEGATION_FILTER
  | OP_RA_RENAME
  | OP_RA_COMPLEMENT
  | OP_RA_SELECT
  | OP_RA_CLONE
  | OP_FD_LT
  | OP_UNINTERPRETED
and decl_kind = enum_6
and enum_7 =
  | NO_FAILURE
  | UNKNOWN
  | TIMEOUT
  | MEMOUT_WATERMARK
  | CANCELED
  | NUM_CONFLICTS
  | THEORY
  | QUANTIFIERS
and search_failure = enum_7
and enum_8 =
  | PRINT_SMTLIB_FULL
  | PRINT_LOW_LEVEL
  | PRINT_SMTLIB_COMPLIANT
  | PRINT_SMTLIB2_COMPLIANT
and ast_print_mode = enum_8

(**
   

*)
(**
   
   
   

   
   
   
   
   
   
   
   
   
*)
(**
   
*)
(**
   
*)
(**
   
*)
(**
   

   
   
*)
(**
   
   
   

   
   
   
   
   
   
*)
(**
   
*)
(**
   

   
   
   
   
   
*)
(**
   

   (*
   - OP_TRUE The constant true.

   - OP_FALSE The constant false.

   - OP_EQ The equality predicate.

   - OP_DISTINCT The n-ary distinct predicate (every argument is mutually distinct).

   - OP_ITE The ternary if-then-else term.

   - OP_AND n-ary conjunction.

   - OP_OR n-ary disjunction.

   - OP_IFF equivalence (binary).

   - OP_XOR Exclusive or.

   - OP_NOT Negation.

   - OP_IMPLIES Implication.

   - OP_OEQ Binary equivalence modulo namings. This binary predicate is used in proof terms.
        It captures equisatisfiability and equivalence modulo renamings.

   - OP_ANUM Arithmetic numeral.

   - OP_LE <=.

   - OP_GE >=.

   - OP_LT <.

   - OP_GT >.

   - OP_ADD Addition - Binary.

   - OP_SUB Binary subtraction.

   - OP_UMINUS Unary minus.

   - OP_MUL Multiplication - Binary.

   - OP_DIV Division - Binary.

   - OP_IDIV Integer division - Binary.

   - OP_REM Remainder - Binary.

   - OP_MOD Modulus - Binary.

   - OP_TO_REAL Coercion of integer to real - Unary.

   - OP_TO_INT Coercion of real to integer - Unary.

   - OP_IS_INT Check if real is also an integer - Unary.

   - OP_STORE Array store. It satisfies select(store(a,i,v),j) = if i = j then v else select(a,j).
        Array store takes at least 3 arguments. 

   - OP_SELECT Array select. 

   - OP_CONST_ARRAY The constant array. For example, select(const(v),i) = v holds for every v and i. The function is unary.

   - OP_ARRAY_DEFAULT Default value of arrays. For example default(const(v)) = v. The function is unary.

   - OP_ARRAY_MAP Array map operator.
         It satisfies map[f](a1,..,a_n)[i] = f(a1[i],...,a_n[i]) for every i.

   - OP_SET_UNION Set union between two Booelan arrays (two arrays whose range type is Boolean). The function is binary.

   - OP_SET_INTERSECT Set intersection between two Boolean arrays. The function is binary.

   - OP_SET_DIFFERENCE Set difference between two Boolean arrays. The function is binary.

   - OP_SET_COMPLEMENT Set complement of a Boolean array. The function is unary.

   - OP_SET_SUBSET Subset predicate between two Boolean arrays. The relation is binary.

   - OP_AS_ARRAY An array value that behaves as the function graph of the
                    function passed as parameter.

   - OP_BNUM Bit-vector numeral.

   - OP_BIT1 One bit bit-vector.

   - OP_BIT0 Zero bit bit-vector.

   - OP_BNEG Unary minus.

   - OP_BADD Binary addition.

   - OP_BSUB Binary subtraction.

   - OP_BMUL Binary multiplication.
    
   - OP_BSDIV Binary signed division.

   - OP_BUDIV Binary unsigned int division.

   - OP_BSREM Binary signed remainder.

   - OP_BUREM Binary unsigned int remainder.

   - OP_BSMOD Binary signed modulus.

   - OP_BSDIV0 Unary function. bsdiv(x,0) is congruent to bsdiv0(x).

   - OP_BUDIV0 Unary function. budiv(x,0) is congruent to budiv0(x).

   - OP_BSREM0 Unary function. bsrem(x,0) is congruent to bsrem0(x).

   - OP_BUREM0 Unary function. burem(x,0) is congruent to burem0(x).

   - OP_BSMOD0 Unary function. bsmod(x,0) is congruent to bsmod0(x).
    
   - OP_ULEQ Unsigned bit-vector <= - Binary relation.

   - OP_SLEQ Signed bit-vector  <= - Binary relation.

   - OP_UGEQ Unsigned bit-vector  >= - Binary relation.

   - OP_SGEQ Signed bit-vector  >= - Binary relation.

   - OP_ULT Unsigned bit-vector  < - Binary relation.

   - OP_SLT Signed bit-vector < - Binary relation.

   - OP_UGT Unsigned bit-vector > - Binary relation.

   - OP_SGT Signed bit-vector > - Binary relation.

   - OP_BAND Bit-wise and - Binary.

   - OP_BOR Bit-wise or - Binary.

   - OP_BNOT Bit-wise not - Unary.

   - OP_BXOR Bit-wise xor - Binary.

   - OP_BNAND Bit-wise nand - Binary.

   - OP_BNOR Bit-wise nor - Binary.

   - OP_BXNOR Bit-wise xnor - Binary.

   - OP_CONCAT Bit-vector concatenation - Binary.

   - OP_SIGN_EXT Bit-vector sign extension.

   - OP_ZERO_EXT Bit-vector zero extension.

   - OP_EXTRACT Bit-vector extraction.

   - OP_REPEAT Repeat bit-vector n times.

   - OP_BREDOR Bit-vector reduce or - Unary.

   - OP_BREDAND Bit-vector reduce and - Unary.

   - OP_BCOMP .

   - OP_BSHL Shift left.

   - OP_BLSHR Logical shift right.

   - OP_BASHR Arithmetical shift right.

   - OP_ROTATE_LEFT Left rotation.

   - OP_ROTATE_RIGHT Right rotation.

   - OP_EXT_ROTATE_LEFT (extended) Left rotation. Similar to OP_ROTATE_LEFT, but it is a binary operator instead of a parametric one.

   - OP_EXT_ROTATE_RIGHT (extended) Right rotation. Similar to OP_ROTATE_RIGHT, but it is a binary operator instead of a parametric one.

   - OP_INT2BV Coerce integer to bit-vector. NB. This function
       is not supported by the decision procedures. Only the most
       rudimentary simplification rules are applied to this function.

   - OP_BV2INT Coerce bit-vector to integer. NB. This function
       is not supported by the decision procedures. Only the most
       rudimentary simplification rules are applied to this function.

   - OP_CARRY Compute the carry bit in a full-adder. 
       The meaning is given by the equivalence
       (carry l1 l2 l3) <=> (or (and l1 l2) (and l1 l3) (and l2 l3)))

   - OP_XOR3 Compute ternary XOR.
       The meaning is given by the equivalence
       (xor3 l1 l2 l3) <=> (xor (xor l1 l2) l3)

   - OP_PR_TRUE: Proof for the expression 'true'.

   - OP_PR_ASSERTED: Proof for a fact asserted by the user.
   
   - OP_PR_GOAL: Proof for a fact (tagged as goal) asserted by the user.

   - OP_PR_MODUS_PONENS: Given a proof for p and a proof for (implies p q), produces a proof for q.
       {e
          T1: p
          T2: (implies p q)
          [mp T1 T2]: q
          }
          The second antecedents may also be a proof for (iff p q).

   - OP_PR_REFLEXIVITY: A proof for (R t t), where R is a reflexive relation. This proof object has no antecedents.
        The only reflexive relations that are used are 
        equivalence modulo namings, equality and equivalence.
        That is, R is either '~', '=' or 'iff'.

   - OP_PR_SYMMETRY: Given an symmetric relation R and a proof for (R t s), produces a proof for (R s t).
          {e
          T1: (R t s)
          [symmetry T1]: (R s t)
          }
          T1 is the antecedent of this proof object.

   - OP_PR_TRANSITIVITY: Given a transitive relation R, and proofs for (R t s) and (R s u), produces a proof
       for (R t u).
       {e
       T1: (R t s)
       T2: (R s u)
       [trans T1 T2]: (R t u)
       }

   - OP_PR_TRANSITIVITY_STAR: Condensed transitivity proof. This proof object is only used if the parameter PROOF_MODE is 1.
     It combines several symmetry and transitivity proofs. 

          Example:
          {e
          T1: (R a b)
          T2: (R c b)
          T3: (R c d)
          [trans* T1 T2 T3]: (R a d)
          }
          R must be a symmetric and transitive relation.

          Assuming that this proof object is a proof for (R s t), then
          a proof checker must check if it is possible to prove (R s t)
          using the antecedents, symmetry and transitivity.  That is, 
          if there is a path from s to t, if we view every
          antecedent (R a b) as an edge between a and b.

   - OP_PR_MONOTONICITY: Monotonicity proof object.
          {e
          T1: (R t_1 s_1)
          ...
          Tn: (R t_n s_n)
          [monotonicity T1 ... Tn]: (R (f t_1 ... t_n) (f s_1 ... s_n))
          }
          Remark: if t_i == s_i, then the antecedent Ti is suppressed.
          That is, reflexivity proofs are supressed to save space.

   - OP_PR_QUANT_INTRO: Given a proof for (~ p q), produces a proof for (~ (forall (x) p) (forall (x) q)).

       T1: (~ p q)
       [quant-intro T1]: (~ (forall (x) p) (forall (x) q))
   
   - OP_PR_DISTRIBUTIVITY: Distributivity proof object. 
          Given that f (= or) distributes over g (= and), produces a proof for

          (= (f a (g c d))
             (g (f a c) (f a d)))

          If f and g are associative, this proof also justifies the following equality:

          (= (f (g a b) (g c d))
             (g (f a c) (f a d) (f b c) (f b d)))

          where each f and g can have arbitrary number of arguments.

          This proof object has no antecedents.
          Remark. This rule is used by the CNF conversion pass and 
          instantiated by f = or, and g = and.
    
   - OP_PR_AND_ELIM: Given a proof for (and l_1 ... l_n), produces a proof for l_i
        
       {e
       T1: (and l_1 ... l_n)
       [and-elim T1]: l_i
       }
   - OP_PR_NOT_OR_ELIM: Given a proof for (not (or l_1 ... l_n)), produces a proof for (not l_i).

       {e
       T1: (not (or l_1 ... l_n))
       [not-or-elim T1]: (not l_i)
       }

   - OP_PR_REWRITE: A proof for a local rewriting step (= t s).
          The head function symbol of t is interpreted.

          This proof object has no antecedents.
          The conclusion of a rewrite rule is either an equality (= t s), 
          an equivalence (iff t s), or equi-satisfiability (~ t s).
          Remark: if f is bool, then = is iff.
          

          Examples:
          {e
          (= (+ x 0) x)
          (= (+ x 1 2) (+ 3 x))
          (iff (or x false) x)
          }

   - OP_PR_REWRITE_STAR: A proof for rewriting an expression t into an expression s.
       This proof object is used if the parameter PROOF_MODE is 1.
       This proof object can have n antecedents.
       The antecedents are proofs for equalities used as substitution rules.
       The object is also used in a few cases if the parameter PROOF_MODE is 2.
       The cases are:
         - When applying contextual simplification (CONTEXT_SIMPLIFIER=true)
         - When converting bit-vectors to Booleans (BIT2BOOL=true)
         - When pulling ite expression up (PULL_CHEAP_ITE_TREES=true)

   - OP_PR_PULL_QUANT: A proof for (iff (f (forall (x) q(x)) r) (forall (x) (f (q x) r))). This proof object has no antecedents.

   - OP_PR_PULL_QUANT_STAR: A proof for (iff P Q) where Q is in prenex normal form.
       This proof object is only used if the parameter PROOF_MODE is 1.       
       This proof object has no antecedents.
  
   - OP_PR_PUSH_QUANT: A proof for:

       {e
          (iff (forall (x_1 ... x_m) (and p_1[x_1 ... x_m] ... p_n[x_1 ... x_m]))
               (and (forall (x_1 ... x_m) p_1[x_1 ... x_m])
                 ... 
               (forall (x_1 ... x_m) p_n[x_1 ... x_m])))
               }
         This proof object has no antecedents.

   - OP_PR_ELIM_UNUSED_VARS:  
          A proof for (iff (forall (x_1 ... x_n y_1 ... y_m) p[x_1 ... x_n])
                           (forall (x_1 ... x_n) p[x_1 ... x_n])) 

          It is used to justify the elimination of unused variables.
          This proof object has no antecedents.

   - OP_PR_DER: A proof for destructive equality resolution:
          (iff (forall (x) (or (not (= x t)) P[x])) P[t])
          if x does not occur in t.

          This proof object has no antecedents.
          
          Several variables can be eliminated simultaneously.

   - OP_PR_QUANT_INST: A proof of (or (not (forall (x) (P x))) (P a))

   - OP_PR_HYPOTHESIS: Mark a hypothesis in a natural deduction style proof.

   - OP_PR_LEMMA: 

       {e
          T1: false
          [lemma T1]: (or (not l_1) ... (not l_n))
          }
          This proof object has one antecedent: a hypothetical proof for false.
          It converts the proof in a proof for (or (not l_1) ... (not l_n)),
          when T1 contains the hypotheses: l_1, ..., l_n.

   - OP_PR_UNIT_RESOLUTION: 
       {e
          T1:      (or l_1 ... l_n l_1' ... l_m')
          T2:      (not l_1)
          ...
          T(n+1):  (not l_n)
          [unit-resolution T1 ... T(n+1)]: (or l_1' ... l_m')
          }

   - OP_PR_IFF_TRUE: 
      {e
       T1: p
       [iff-true T1]: (iff p true)
       }

   - OP_PR_IFF_FALSE:
      {e
       T1: (not p)
       [iff-false T1]: (iff p false)
       }

   - OP_PR_COMMUTATIVITY:

          [comm]: (= (f a b) (f b a))
          
          f is a commutative operator.

          This proof object has no antecedents.
          Remark: if f is bool, then = is iff.
   
   - OP_PR_DEF_AXIOM: Proof object used to justify Tseitin's like axioms:
       
          {e
          (or (not (and p q)) p)
          (or (not (and p q)) q)
          (or (not (and p q r)) p)
          (or (not (and p q r)) q)
          (or (not (and p q r)) r)
          ...
          (or (and p q) (not p) (not q))
          (or (not (or p q)) p q)
          (or (or p q) (not p))
          (or (or p q) (not q))
          (or (not (iff p q)) (not p) q)
          (or (not (iff p q)) p (not q))
          (or (iff p q) (not p) (not q))
          (or (iff p q) p q)
          (or (not (ite a b c)) (not a) b)
          (or (not (ite a b c)) a c)
          (or (ite a b c) (not a) (not b))
          (or (ite a b c) a (not c))
          (or (not (not a)) (not a))
          (or (not a) a)
          }
          This proof object has no antecedents.
          Note: all axioms are propositional tautologies.
          Note also that 'and' and 'or' can take multiple arguments.
          You can recover the propositional tautologies by
          unfolding the Boolean connectives in the axioms a small
          bounded number of steps (=3).
    
   - OP_PR_DEF_INTRO: Introduces a name for a formula/term.
       Suppose e is an expression with free variables x, and def-intro
       introduces the name n(x). The possible cases are:

       When e is of Boolean type:
       [def-intro]: (and (or n (not e)) (or (not n) e))

       or:
       [def-intro]: (or (not n) e)
       when e only occurs positively.

       When e is of the form (ite cond th el):
       [def-intro]: (and (or (not cond) (= n th)) (or cond (= n el)))

       Otherwise:
       [def-intro]: (= n e)       

   - OP_PR_APPLY_DEF: 
       [apply-def T1]: F ~ n
       F is 'equivalent' to n, given that T1 is a proof that
       n is a name for F.
   
   - OP_PR_IFF_OEQ:
       T1: (iff p q)
       [iff~ T1]: (~ p q)
 
   - OP_PR_NNF_POS: Proof for a (positive) NNF step. Example:
       {e
          T1: (not s_1) ~ r_1
          T2: (not s_2) ~ r_2
          T3: s_1 ~ r_1'
          T4: s_2 ~ r_2'
          [nnf-pos T1 T2 T3 T4]: (~ (iff s_1 s_2)
                                    (and (or r_1 r_2') (or r_1' r_2)))
          }
       The negation normal form steps NNF_POS and NNF_NEG are used in the following cases:
       (a) When creating the NNF of a positive force quantifier.
        The quantifier is retained (unless the bound variables are eliminated).
        Example
        {e
           T1: q ~ q_new 
           [nnf-pos T1]: (~ (forall (x T) q) (forall (x T) q_new))
        }
       (b) When recursively creating NNF over Boolean formulas, where the top-level
       connective is changed during NNF conversion. The relevant Boolean connectives
       for NNF_POS are 'implies', 'iff', 'xor', 'ite'.
       NNF_NEG furthermore handles the case where negation is pushed
       over Boolean connectives 'and' and 'or'.

    
   - OP_PR_NFF_NEG: Proof for a (negative) NNF step. Examples:
          {e
          T1: (not s_1) ~ r_1
          ...
          Tn: (not s_n) ~ r_n
         [nnf-neg T1 ... Tn]: (not (and s_1 ... s_n)) ~ (or r_1 ... r_n)
      and
          T1: (not s_1) ~ r_1
          ...
          Tn: (not s_n) ~ r_n
         [nnf-neg T1 ... Tn]: (not (or s_1 ... s_n)) ~ (and r_1 ... r_n)
      and
          T1: (not s_1) ~ r_1
          T2: (not s_2) ~ r_2
          T3: s_1 ~ r_1'
          T4: s_2 ~ r_2'
         [nnf-neg T1 T2 T3 T4]: (~ (not (iff s_1 s_2))
                                   (and (or r_1 r_2) (or r_1' r_2')))
       }
   - OP_PR_NNF_STAR: A proof for (~ P Q) where Q is in negation normal form.
       
       This proof object is only used if the parameter PROOF_MODE is 1.       
              
       This proof object may have n antecedents. Each antecedent is a PR_DEF_INTRO.

   - OP_PR_CNF_STAR: A proof for (~ P Q) where Q is in conjunctive normal form.
       This proof object is only used if the parameter PROOF_MODE is 1.       
       This proof object may have n antecedents. Each antecedent is a PR_DEF_INTRO.          

   - OP_PR_SKOLEMIZE: Proof for:  
       
          {e
          [sk]: (~ (not (forall x (p x y))) (not (p (sk y) y)))
          [sk]: (~ (exists x (p x y)) (p (sk y) y))
          }

          This proof object has no antecedents.
   
   - OP_PR_MODUS_PONENS_OEQ: Modus ponens style rule for equi-satisfiability.
       {e
          T1: p
          T2: (~ p q)
          [mp~ T1 T2]: q
          }

    - OP_PR_TH_LEMMA: Generic proof for theory lemmas.

         The theory lemma function comes with one or more parameters.
         The first parameter indicates the name of the theory.
         For the theory of arithmetic, additional parameters provide hints for
         checking the theory lemma. 
         The hints for arithmetic are:
         
         - farkas - followed by rational coefficients. Multiply the coefficients to the
           inequalities in the lemma, add the (negated) inequalities and obtain a contradiction.

         - triangle-eq - Indicates a lemma related to the equivalence:
         {e
            (iff (= t1 t2) (and (<= t1 t2) (<= t2 t1)))
         }

         - gcd-test - Indicates an integer linear arithmetic lemma that uses a gcd test.


      - OP_RA_STORE: Insert a record into a relation.
        The function takes n+1 arguments, where the first argument is the relation and the remaining n elements 
        correspond to the n columns of the relation.

      - OP_RA_EMPTY: Creates the empty relation. 
        
      - OP_RA_IS_EMPTY: Tests if the relation is empty.

      - OP_RA_JOIN: Create the relational join.

      - OP_RA_UNION: Create the union or convex hull of two relations. 
        The function takes two arguments.

      - OP_RA_WIDEN: Widen two relations.
        The function takes two arguments.

      - OP_RA_PROJECT: Project the columns (provided as numbers in the parameters).
        The function takes one argument.

      - OP_RA_FILTER: Filter (restrict) a relation with respect to a predicate.
        The first argument is a relation. 
        The second argument is a predicate with free de-Brujin indices
        corresponding to the columns of the relation.
        So the first column in the relation has index 0.

      - OP_RA_NEGATION_FILTER: Intersect the first relation with respect to negation
        of the second relation (the function takes two arguments).
        Logically, the specification can be described by a function

           target = filter_by_negation(pos, neg, columns)

        where columns are pairs c1, d1, .., cN, dN of columns from pos and neg, such that
        target are elements in x in pos, such that there is no y in neg that agrees with
        x on the columns c1, d1, .., cN, dN.

    
      - OP_RA_RENAME: rename columns in the relation. 
        The function takes one argument.
        The parameters contain the renaming as a cycle.
         
      - OP_RA_COMPLEMENT: Complement the relation.

      - OP_RA_SELECT: Check if a record is an element of the relation.
        The function takes n+1 arguments, where the first argument is a relation,
        and the remaining n arguments correspond to a record.

      - OP_RA_CLONE: Create a fresh copy (clone) of a relation. 
        
        
        
        

      - OP_FD_LT: A less than predicate over the finite domain FINITE_DOMAIN_SORT.

    *)

*)
(**
   

   
   
   
   
   
   
   
   
*)
(**
   

   
   
   
   
*)
(** 
        {2 {L Create configuration}}
    *)
(**
       Summary: Create a configuration.

       Configurations are created in order to assign parameters prior to creating 
       contexts for Z3 interaction. For example, if the users whishes to use model
       generation, then call:

       [set_param_value cfg "MODEL" "true"]

        - {b Remarks}: Consider using {!Z3.mk_context_x} instead of using
       explicit configuration objects. The function {!Z3.mk_context_x}
       receives an array of string pairs. This array represents the
       configuration options. 

       - {b See also}: {!Z3.set_param_value}
       - {b See also}: {!Z3.del_config}
    *)
external mk_config : unit -> config
	= "camlidl_z3_Z3_mk_config"

(**
       Summary: Delete the given configuration object.

       - {b See also}: {!Z3.mk_config}
    *)
external del_config : config -> unit
	= "camlidl_z3_Z3_del_config"

(**
       Summary: Set a configuration parameter.

       The list of all configuration parameters can be obtained using the Z3 executable:

       {v 
       z3.exe -ini?
        v}

       - {b See also}: {!Z3.mk_config}
    *)
external set_param_value : config -> string -> string -> unit
	= "camlidl_z3_Z3_set_param_value"

(**
       {2 {L Create context}}
    *)
(**
       Summary: Create a context using the given configuration. 
    
       After a context is created, the configuration cannot be changed.
       All main interaction with Z3 happens in the context of a context.

        - {b Remarks}: Consider using {!Z3.mk_context_x} instead of using
       explicit configuration objects. The function {!Z3.mk_context_x}
       receives an array of string pairs. This array represents the
       configuration options. 

       - {b See also}: {!Z3.del_context}
    *)
external mk_context : config -> context
	= "camlidl_z3_Z3_mk_context"

(**
       Summary: Create a context using the given configuration.
       This function is similar to {!Z3.mk_context}. However,
       in the context returned by this function, the user
       is responsible for managing ast reference counters.
       Managing reference counters is a burden and error-prone,
       but allows the user to use the memory more efficiently. 
       The user must invoke {!Z3.inc_ref} for any ast returned
       by Z3, and {!Z3.dec_ref} whenever the ast is not needed
       anymore. This idiom is similar to the one used in
       BDD (binary decision diagrams) packages such as CUDD.

       Remark: sort, func_decl, app, pattern are
       ast's.
 
       After a context is created, the configuration cannot be changed.
       All main interaction with Z3 happens in the context of a context.
    *)
external mk_context_rc : config -> context
	= "camlidl_z3_Z3_mk_context_rc"

(**
       Summary: Set the SMTLIB logic to be used in the given logical context.
       It is incorrect to invoke this function after invoking
       {!Z3.check}, {!Z3.check_and_get_model}, {!Z3.check_assumptions} and {!Z3.push}.
       Return TRUE if the logic was changed successfully, and FALSE otherwise.
    *)
external set_logic : context -> string -> bool
	= "camlidl_z3_Z3_set_logic"

(**
       Summary: Delete the given logical context.

       - {b See also}: {!Z3.mk_config}
    *)
external del_context : context -> unit
	= "camlidl_z3_Z3_del_context"

(**
       Summary: Increment the reference counter of the given AST.
       The context c should have been created using {!Z3.mk_context_rc}.
       This function is a NOOP if c was created using {!Z3.mk_context}.
    *)
external inc_ref : context -> ast -> unit
	= "camlidl_z3_Z3_inc_ref"

(**
       Summary: Decrement the reference counter of the given AST.
       The context c should have been created using {!Z3.mk_context_rc}.
       This function is a NOOP if c was created using {!Z3.mk_context}.
    *)
external dec_ref : context -> ast -> unit
	= "camlidl_z3_Z3_dec_ref"

(**
       Summary: Enable trace messages to a file

       When trace messages are enabled, Z3 will record the operations performed on a context in the given file file.
       Return TRUE if the file was opened successfully, and FALSE otherwise.

       - {b See also}: {!Z3.trace_off}
    *)
external trace_to_file : context -> string -> bool
	= "camlidl_z3_Z3_trace_to_file"

(**
       Summary: Enable trace messages to a standard error.

       - {b See also}: {!Z3.trace_off}
    *)
external trace_to_stderr : context -> unit
	= "camlidl_z3_Z3_trace_to_stderr"

(**
       Summary: Enable trace messages to a standard output.

       - {b See also}: {!Z3.trace_off}
    *)
external trace_to_stdout : context -> unit
	= "camlidl_z3_Z3_trace_to_stdout"

(**
       Summary: Disable trace messages.

       - {b See also}: {!Z3.trace_to_file}
       - {b See also}: {!Z3.trace_to_stdout}
       - {b See also}: {!Z3.trace_to_stderr}
    *)
external trace_off : context -> unit
	= "camlidl_z3_Z3_trace_off"

(**
       Summary: Enable/disable printing warning messages to the console.

       Warnings are printed after passing true, warning messages are
       suppressed after calling this method with false.       
    *)
external toggle_warning_messages : bool -> unit
	= "camlidl_z3_Z3_toggle_warning_messages"

(**
       Summary: Update a mutable configuration parameter.

       The list of all configuration parameters can be obtained using the Z3 executable:

       {v 
       z3.exe -ini?
        v}

       Only a few configuration parameters are mutable once the context is created.
       The error handler is invoked when trying to modify an immutable parameter.

       - {b See also}: {!Z3.set_param_value}
    *)
external update_param_value : context -> string -> string -> unit
	= "camlidl_z3_Z3_update_param_value"

(**
       Summary: Get a configuration parameter.
      
       Returns false if the parameter value does not exist.

       - {b See also}: {!Z3.mk_config}
       - {b See also}: {!Z3.set_param_value}
    *)
(**
       {2 {L Symbols}}
    *)
(**
       Summary: Create a Z3 symbol using an integer.

       Symbols are used to name several term and type constructors.

       NB. Not all integers can be passed to this function.
       The legal range of unsigned int integers is 0 to 2^30-1.

       - {b See also}: {!Z3.mk_string_symbol}
    *)
external mk_int_symbol : context -> int -> symbol
	= "camlidl_z3_Z3_mk_int_symbol"

(**
       Summary: Create a Z3 symbol using a C string.

       Symbols are used to name several term and type constructors.

       - {b See also}: {!Z3.mk_int_symbol}
    *)
external mk_string_symbol : context -> string -> symbol
	= "camlidl_z3_Z3_mk_string_symbol"

(**
       {2 {L Sorts}}
    *)
(**
       Summary: compare sorts.
    *)
external is_eq_sort : context -> sort -> sort -> bool
	= "camlidl_z3_Z3_is_eq_sort"

(**
       Summary: Create a free (uninterpreted) type using the given name (symbol).
       
       Two free types are considered the same iff the have the same name.
    *)
external mk_uninterpreted_sort : context -> symbol -> sort
	= "camlidl_z3_Z3_mk_uninterpreted_sort"

(**
       Summary: Create the Boolean type. 

       This type is used to create propositional variables and predicates.
    *)
external mk_bool_sort : context -> sort
	= "camlidl_z3_Z3_mk_bool_sort"

(**
       Summary: Create an integer type.

       This type is not the int type found in programming languages.
       A machine integer can be represented using bit-vectors. The function
       {!Z3.mk_bv_sort} creates a bit-vector type.

       - {b See also}: {!Z3.mk_bv_sort}
    *)
external mk_int_sort : context -> sort
	= "camlidl_z3_Z3_mk_int_sort"

(**
       Summary: Create a real type. 

       This type is not a floating point number.
       Z3 does not have support for floating point numbers yet.
    *)
external mk_real_sort : context -> sort
	= "camlidl_z3_Z3_mk_real_sort"

(**
       Summary: Create a bit-vector type of the given size.
    
       This type can also be seen as a machine integer.

       - {b Remarks}: The size of the bitvector type must be greater than zero.
    *)
external mk_bv_sort : context -> int -> sort
	= "camlidl_z3_Z3_mk_bv_sort"

(**
       Summary: Create an array type. 
       
       We usually represent the array type as: {e [domain -> range] }.
       Arrays are usually used to model the heap/memory in software verification.

       - {b See also}: {!Z3.mk_select}
       - {b See also}: {!Z3.mk_store}
    *)
external mk_array_sort : context -> sort -> sort -> sort
	= "camlidl_z3_Z3_mk_array_sort"

(**
       Summary: Create a tuple type.
       
        [mk_tuple_sort c name field_names field_sorts] creates a tuple with a constructor named [name],
       a [n] fields, where [n] is the size of the arrays [field_names] and [field_sorts].
       

       
       

       
       
       
       
       
       
       
    *)
external mk_tuple_sort : context -> symbol -> symbol array -> sort array -> sort * func_decl * func_decl array
	= "camlidl_z3_Z3_mk_tuple_sort"

(**
       Summary: Create a enumeration sort.
       
        [mk_enumeration_sort c enums] creates an enumeration sort with enumeration names [enums], 
               it also returns [n] predicates, where [n] is the number of [enums] corresponding
               to testing whether an element is one of the enumerants.
       

       
       

       
       
       
       
       
       
    *)
external mk_enumeration_sort : context -> symbol -> symbol array -> sort * func_decl array * func_decl array
	= "camlidl_z3_Z3_mk_enumeration_sort"

(**
       Summary: Create a list sort
       
        [mk_list_sort c name elem_sort] creates a list sort of [name], over elements of sort [elem_sort].
       

       
       

       
       
       
       
       
       
       
       
       
    *)
external mk_list_sort : context -> symbol -> sort -> sort * func_decl * func_decl * func_decl * func_decl * func_decl * func_decl
	= "camlidl_z3_Z3_mk_list_sort"

(**
       Summary: Create a constructor.
       
       
       
       
       
       
       
       
                        sort reference is 0, then the value in sort_refs should be an index referring to 
                        one of the recursive datatypes that is declared.                        
    *)
external mk_constructor : context -> symbol -> symbol -> symbol array -> sort array -> int array -> constructor
	= "camlidl_z3_Z3_mk_constructor_bytecode" "camlidl_z3_Z3_mk_constructor"

(**
       Summary: Query constructor for declared funcions.
       
       
       
       
       
       
       
    *)
external query_constructor : context -> constructor -> int -> func_decl * func_decl * func_decl array
	= "camlidl_z3_Z3_query_constructor"

(**
       Summary: Reclaim memory allocated to constructor.

       
       
    *)
external del_constructor : context -> constructor -> unit
	= "camlidl_z3_Z3_del_constructor"

(**
       Summary: Create recursive datatype. Return the datatype sort.

       
	   
       
       
    *)
external mk_datatype : context -> symbol -> constructor array -> sort * constructor array
	= "camlidl_z3_Z3_mk_datatype"

(**
       Summary: Create list of constructors.

       
       
       
    *)
external mk_constructor_list : context -> constructor array -> constructor_list
	= "camlidl_z3_Z3_mk_constructor_list"

(**
       Summary: reclaim memory allocated for constructor list.

       Each constructor inside the constructor list must be independently reclaimed using {!Z3.del_constructor}.

       
       

    *)
external del_constructor_list : context -> constructor_list -> unit
	= "camlidl_z3_Z3_del_constructor_list"

(**
       Summary: Create mutually recursive datatypes.

       
       
       
       
       
    *)
external mk_datatypes : context -> symbol array -> constructor_list array -> sort array * constructor_list array
	= "camlidl_z3_Z3_mk_datatypes"

(**
       {2 {L Injective functions}}
    *)
(**
       Summary: Create injective function declaration
    *)
external mk_injective_function : context -> symbol -> sort array -> sort -> func_decl
	= "camlidl_z3_Z3_mk_injective_function"

(**
       {2 {L Constants and Applications}}
     *)
(**
       Summary: compare terms.
    *)
external is_eq_ast : context -> ast -> ast -> bool
	= "camlidl_z3_Z3_is_eq_ast"

(**
       Summary: compare terms.
    *)
external is_eq_func_decl : context -> func_decl -> func_decl -> bool
	= "camlidl_z3_Z3_is_eq_func_decl"

(**
       Summary: Declare a constant or function.

        [mk_func_decl c n d r] creates a function with name [n], domain [d], and range [r].
       The arity of the function is the size of the array [d]. 

       
       
       
       
       

       After declaring a constant or function, the function
       {!Z3.mk_app} can be used to create a constant or function
       application.

       - {b See also}: {!Z3.mk_app}
    *)
external mk_func_decl : context -> symbol -> sort array -> sort -> func_decl
	= "camlidl_z3_Z3_mk_func_decl"

(**
       Summary: Create a constant or function application.

       - {b See also}: {!Z3.mk_func_decl}
    *)
external mk_app : context -> func_decl -> ast array -> ast
	= "camlidl_z3_Z3_mk_app"

(**
       Summary: Declare and create a constant.
       
       
       
       
       
       
       
        [mk_const c s t] is a shorthand for [mk_app c (mk_func_decl c s [||] t) [||]] 

       - {b See also}: {!Z3.mk_func_decl}
       - {b See also}: {!Z3.mk_app}
    *)
external mk_const : context -> symbol -> sort -> ast
	= "camlidl_z3_Z3_mk_const"

(**
       Summary: Create a labeled formula.

       
       
       
       

       A label behaves as an identity function, so the truth value of the 
       labeled formula is unchanged. Labels are used for identifying 
       useful sub-formulas when generating counter-examples.
    *)
external mk_label : context -> symbol -> bool -> ast -> ast
	= "camlidl_z3_Z3_mk_label"

(**
       Summary: Declare a fresh constant or function.

       Z3 will generate an unique name for this function declaration.
       
       
       

       - {b See also}: {!Z3.mk_func_decl}
    *)
external mk_fresh_func_decl : context -> string -> sort array -> sort -> func_decl
	= "camlidl_z3_Z3_mk_fresh_func_decl"

(**
       Summary: Declare and create a fresh constant.
       
       
       

        [mk_fresh_const c p t] is a shorthand for [mk_app c (mk_fresh_func_decl c p [||] t) [||]]. 

       
       
       - {b See also}: {!Z3.mk_func_decl}
       - {b See also}: {!Z3.mk_app}
    *)
external mk_fresh_const : context -> string -> sort -> ast
	= "camlidl_z3_Z3_mk_fresh_const"

(** 
        Summary: Create an AST node representing true.
    *)
external mk_true : context -> ast
	= "camlidl_z3_Z3_mk_true"

(** 
        Summary: Create an AST node representing false.
    *)
external mk_false : context -> ast
	= "camlidl_z3_Z3_mk_false"

(** 
        Summary: \[ [ mk_eq c l r ] \]
        Create an AST node representing {e l = r }.
        
        The nodes l and r must have the same type. 
    *)
external mk_eq : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_eq"

(**
       
        Summary: \[ [mk_distinct c [| t_1; ...; t_n |]] \] Create an AST
       node represeting a distinct construct. It is used for declaring
       the arguments t_i pairwise distinct. 

       
       
       
       All arguments must have the same sort.

       - {b Remarks}: The number of arguments of a distinct construct must be greater than one.
    *)
external mk_distinct : context -> ast array -> ast
	= "camlidl_z3_Z3_mk_distinct"

(** 
        Summary: \[ [ mk_not c a ] \] 
        Create an AST node representing {e not(a) }.
        
        The node a must have Boolean sort.
    *)
external mk_not : context -> ast -> ast
	= "camlidl_z3_Z3_mk_not"

(**
       Summary: \[ [ mk_ite c t1 t2 t2 ] \] 
       Create an AST node representing an if-then-else: {e ite(t1, t2,
       t3) }.

       The node t1 must have Boolean sort, t2 and t3 must have the same sort.
       The sort of the new node is equal to the sort of t2 and t3.
    *)
external mk_ite : context -> ast -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_ite"

(**
       Summary: \[ [ mk_iff c t1 t2 ] \]
       Create an AST node representing {e t1 iff t2 }.

       The nodes t1 and t2 must have Boolean sort.
    *)
external mk_iff : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_iff"

(**
       Summary: \[ [ mk_implies c t1 t2 ] \]
       Create an AST node representing {e t1 implies t2 }.

       The nodes t1 and t2 must have Boolean sort.
    *)
external mk_implies : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_implies"

(**
       Summary: \[ [ mk_xor c t1 t2 ] \]
       Create an AST node representing {e t1 xor t2 }.

       The nodes t1 and t2 must have Boolean sort.
    *)
external mk_xor : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_xor"

(**
       
        Summary: \[ [mk_and c [| t_1; ...; t_n |]] \] Create the conjunction: {e t_1 and ... and t_n}. 

       
       All arguments must have Boolean sort.
       
       - {b Remarks}: The number of arguments must be greater than zero.
    *)
external mk_and : context -> ast array -> ast
	= "camlidl_z3_Z3_mk_and"

(**
       
        Summary: \[ [mk_or c [| t_1; ...; t_n |]] \] Create the disjunction: {e t_1 or ... or t_n}. 

       
       All arguments must have Boolean sort.

       - {b Remarks}: The number of arguments must be greater than zero.
    *)
external mk_or : context -> ast array -> ast
	= "camlidl_z3_Z3_mk_or"

(**
       
        Summary: \[ [mk_add c [| t_1; ...; t_n |]] \] Create the term: {e t_1 + ... + t_n}. 

       
       All arguments must have int or real sort.

       - {b Remarks}: The number of arguments must be greater than zero.
    *)
external mk_add : context -> ast array -> ast
	= "camlidl_z3_Z3_mk_add"

(**
       
        Summary: \[ [mk_mul c [| t_1; ...; t_n |]] \] Create the term: {e t_1 * ... * t_n}. 

       
       All arguments must have int or real sort.
       
       - {b Remarks}: Z3 has limited support for non-linear arithmetic.
       - {b Remarks}: The number of arguments must be greater than zero.
    *)
external mk_mul : context -> ast array -> ast
	= "camlidl_z3_Z3_mk_mul"

(**
       
        Summary: \[ [mk_sub c [| t_1; ...; t_n |]] \] Create the term: {e t_1 - ... - t_n}. 

       
       All arguments must have int or real sort.

       - {b Remarks}: The number of arguments must be greater than zero.
    *)
external mk_sub : context -> ast array -> ast
	= "camlidl_z3_Z3_mk_sub"

(**
       
        Summary: \[ [mk_unary_minus c arg] \] Create the term: {e - arg}. 

       The argument must have int or real type.

    *)
external mk_unary_minus : context -> ast -> ast
	= "camlidl_z3_Z3_mk_unary_minus"

(**
       
        Summary: \[ [mk_div c t_1 t_2] \] Create the term: {e t_1 div t_2}. 

       The arguments must either both have int type or both have real type.
       If the arguments have int type, then the result type is an int type, otherwise the
       the result type is real.

    *)
external mk_div : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_div"

(**
       
        Summary: \[ [mk_mod c t_1 t_2] \] Create the term: {e t_1 mod t_2}. 

       The arguments must have int type.

    *)
external mk_mod : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_mod"

(**
       
        Summary: \[ [mk_rem c t_1 t_2] \] Create the term: {e t_1 rem t_2}. 

       The arguments must have int type.

    *)
external mk_rem : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_rem"

(** 
        Summary: \[ [ mk_lt c t1 t2 ] \] 
        Create less than.

        The nodes t1 and t2 must have the same sort, and must be int or real.
    *)
external mk_lt : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_lt"

(** 
        Summary: \[ [ mk_le c t1 t2 ] \]
        Create less than or equal to.
        
        The nodes t1 and t2 must have the same sort, and must be int or real.
    *)
external mk_le : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_le"

(** 
        Summary: \[ [ mk_gt c t1 t2 ] \]
        Create greater than.
        
        The nodes t1 and t2 must have the same sort, and must be int or real.
    *)
external mk_gt : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_gt"

(** 
        Summary: \[ [ mk_ge c t1 t2 ] \]
        Create greater than or equal to.
        
        The nodes t1 and t2 must have the same sort, and must be int or real.
    *)
external mk_ge : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_ge"

(** 
        Summary: \[ [ mk_int2real c t1 ] \]
        Coerce an integer to a real.

        There is also a converse operation exposed.
        It follows the semantics prescribed by the SMT-LIB standard.

        You can take the floor of a real by 
        creating an auxiliary integer constant k and
        and asserting {e  mk_int2real(k) <= t1 < mk_int2real(k)+1 }.
        
        The node t1 must have sort integer.

        - {b See also}: {!Z3.mk_real2int}
        - {b See also}: {!Z3.mk_is_int}
    *)
external mk_int2real : context -> ast -> ast
	= "camlidl_z3_Z3_mk_int2real"

(** 
        Summary: \[ [ mk_real2int c t1 ] \]
        Coerce a real to an integer.

        The semantics of this function follows the SMT-LIB standard
        for the function to_int

        - {b See also}: {!Z3.mk_int2real}
        - {b See also}: {!Z3.mk_is_int}
    *)
external mk_real2int : context -> ast -> ast
	= "camlidl_z3_Z3_mk_real2int"

(** 
        Summary: \[ [ mk_is_int c t1 ] \]
        Check if a real number is an integer.

        - {b See also}: {!Z3.mk_int2real}
        - {b See also}: {!Z3.mk_real2int}
    *)
external mk_is_int : context -> ast -> ast
	= "camlidl_z3_Z3_mk_is_int"

(**
       Summary: \[ [ mk_bvnot c t1 ] \]
       Bitwise negation.

       The node t1 must have a bit-vector sort.
    *)
external mk_bvnot : context -> ast -> ast
	= "camlidl_z3_Z3_mk_bvnot"

(**
       Summary: \[ [ mk_bvredand c t1 ] \]
       Take conjunction of bits in vector, return vector of length 1.

       The node t1 must have a bit-vector sort.
    *)
external mk_bvredand : context -> ast -> ast
	= "camlidl_z3_Z3_mk_bvredand"

(**
       Summary: \[ [ mk_bvredor c t1 ] \]
       Take disjunction of bits in vector, return vector of length 1.

       The node t1 must have a bit-vector sort.
    *)
external mk_bvredor : context -> ast -> ast
	= "camlidl_z3_Z3_mk_bvredor"

(**
       Summary: \[ [ mk_bvand c t1 t2 ] \]
       Bitwise and.

       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvand : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvand"

(**
       Summary: \[ [ mk_bvor c t1 t2 ] \]
       Bitwise or.

       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvor : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvor"

(**
       Summary: \[ [ mk_bvxor c t1 t2 ] \]
       Bitwise exclusive-or.

       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvxor : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvxor"

(**
       Summary: \[ [ mk_bvnand c t1 t2 ] \]
       Bitwise nand. 

       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvnand : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvnand"

(**
       Summary: \[ [ mk_bvnor c t1 t2 ] \]
       Bitwise nor. 

       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvnor : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvnor"

(**
       Summary: \[ [ mk_bvxnor c t1 t2 ] \]
       Bitwise xnor. 
       
       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvxnor : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvxnor"

(**
       Summary: \[ [ mk_bvneg c t1 ] \]
       Standard two's complement unary minus. 

       The node t1 must have bit-vector sort.
    *)
external mk_bvneg : context -> ast -> ast
	= "camlidl_z3_Z3_mk_bvneg"

(** 
        Summary: \[ [ mk_bvadd c t1 t2 ] \]
        Standard two's complement addition.
        
        The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvadd : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvadd"

(** 
        Summary: \[ [ mk_bvsub c t1 t2 ] \]
        Standard two's complement subtraction.
        
        The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvsub : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsub"

(** 
        Summary: \[ [ mk_bvmul c t1 t2 ] \]
        Standard two's complement multiplication.
        
        The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvmul : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvmul"

(** 
        Summary: \[ [ mk_bvudiv c t1 t2 ] \]
        Unsigned division. 

        It is defined as the floor of {e t1/t2 } if t2 is
        different from zero. If {e t2 } is zero, then the result
        is undefined.
        
        The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvudiv : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvudiv"

(** 
        Summary: \[ [ mk_bvsdiv c t1 t2 ] \]
        Two's complement signed division. 

        It is defined in the following way:

        - The floor of {e t1/t2 } if t2 is different from zero, and {e t1*t2 >= 0 }.

        - The ceiling of {e t1/t2 } if t2 is different from zero, and {e t1*t2 < 0 }.
        
        If {e t2 } is zero, then the result is undefined.
        
        The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvsdiv : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsdiv"

(**
       Summary: \[ [ mk_bvurem c t1 t2 ] \]
       Unsigned remainder.

       It is defined as {e t1 - (t1 /u t2) * t2 }, where {e /u } represents unsigned int division.
       
       If {e t2 } is zero, then the result is undefined.
       
       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvurem : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvurem"

(**
       Summary: \[ [ mk_bvsrem c t1 t2 ] \]
       Two's complement signed remainder (sign follows dividend).

       It is defined as {e t1 - (t1 /s t2) * t2 }, where {e /s } represents signed division.
       The most significant bit (sign) of the result is equal to the most significant bit of t1.

       If {e t2 } is zero, then the result is undefined.
       
       The nodes t1 and t2 must have the same bit-vector sort.

       - {b See also}: {!Z3.mk_bvsmod}
    *)
external mk_bvsrem : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsrem"

(**
       Summary: \[ [ mk_bvsmod c t1 t2 ] \]
       Two's complement signed remainder (sign follows divisor).
       
       If {e t2 } is zero, then the result is undefined.
       
       The nodes t1 and t2 must have the same bit-vector sort.

       - {b See also}: {!Z3.mk_bvsrem}
    *)
external mk_bvsmod : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsmod"

(**
       Summary: \[ [ mk_bvult c t1 t2 ] \]
       Unsigned less than.

       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvult : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvult"

(**
       Summary: \[ [ mk_bvslt c t1 t2 ] \]
       Two's complement signed less than.
       
       It abbreviates:
       {v 
      (or (and (= (extract[|m-1|:|m-1|] t1) bit1)
               (= (extract[|m-1|:|m-1|] t2) bit0))
          (and (= (extract[|m-1|:|m-1|] t1) (extract[|m-1|:|m-1|] t2))
               (bvult t1 t2)))
        v}

       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvslt : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvslt"

(**
       Summary: \[ [ mk_bvule c t1 t2 ] \]
       Unsigned less than or equal to.

       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvule : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvule"

(**
       Summary: \[ [ mk_bvsle c t1 t2 ] \]
       Two's complement signed less than or equal to.

       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvsle : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsle"

(**
       Summary: \[ [ mk_bvuge c t1 t2 ] \]
       Unsigned greater than or equal to.

       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvuge : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvuge"

(**
       Summary: \[ [ mk_bvsge c t1 t2 ] \]
       Two's complement signed greater than or equal to.

       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvsge : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsge"

(**
       Summary: \[ [ mk_bvugt c t1 t2 ] \]
       Unsigned greater than.

       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvugt : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvugt"

(**
       Summary: \[ [ mk_bvsgt c t1 t2 ] \]
       Two's complement signed greater than.

       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvsgt : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsgt"

(**
       Summary: \[ [ mk_concat c t1 t2 ] \]
       Concatenate the given bit-vectors.
       
       The nodes t1 and t2 must have (possibly different) bit-vector sorts

       The result is a bit-vector of size {e n1+n2 }, where n1 (n2) is the size
       of t1 (t2).
    *)
external mk_concat : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_concat"

(**
       Summary: \[ [ mk_extract c high low t1 ] \]
       Extract the bits high down to low from a bitvector of
       size m to yield a new bitvector of size n, where {e n =
       high - low + 1 }.

       The node t1 must have a bit-vector sort.
    *)
external mk_extract : context -> int -> int -> ast -> ast
	= "camlidl_z3_Z3_mk_extract"

(**
       Summary: \[ [ mk_sign_ext c i t1 ] \]
       Sign-extend of the given bit-vector to the (signed) equivalent bitvector of
       size {e m+i }, where m is the size of the given
       bit-vector.

       The node t1 must have a bit-vector sort.
    *)
external mk_sign_ext : context -> int -> ast -> ast
	= "camlidl_z3_Z3_mk_sign_ext"

(**
       Summary: \[ [ mk_zero_ext c i t1 ] \]
       Extend the given bit-vector with zeros to the (unsigned int) equivalent
       bitvector of size {e m+i }, where m is the size of the
       given bit-vector.
       
       The node t1 must have a bit-vector sort. 
    *)
external mk_zero_ext : context -> int -> ast -> ast
	= "camlidl_z3_Z3_mk_zero_ext"

(**
       Summary: \[ [ mk_repeat c i t1 ] \]
       Repeat the given bit-vector up length {e i }.
       
       The node t1 must have a bit-vector sort. 
    *)
external mk_repeat : context -> int -> ast -> ast
	= "camlidl_z3_Z3_mk_repeat"

(**
       Summary: \[ [ mk_bvshl c t1 t2 ] \]
       Shift left.

       It is equivalent to multiplication by {e 2^x } where x is the value of the
       third argument.

       NB. The semantics of shift operations varies between environments. This 
       definition does not necessarily capture directly the semantics of the 
       programming language or assembly architecture you are modeling.

       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvshl : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvshl"

(**
       Summary: \[ [ mk_bvlshr c t1 t2 ] \]
       Logical shift right.

       It is equivalent to unsigned int division by {e 2^x } where x is the
       value of the third argument.

       NB. The semantics of shift operations varies between environments. This 
       definition does not necessarily capture directly the semantics of the 
       programming language or assembly architecture you are modeling.

       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvlshr : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvlshr"

(**
       Summary: \[ [ mk_bvashr c t1 t2 ] \]
       Arithmetic shift right.
       
       It is like logical shift right except that the most significant
       bits of the result always copy the most significant bit of the
       second argument.

       NB. The semantics of shift operations varies between environments. This 
       definition does not necessarily capture directly the semantics of the 
       programming language or assembly architecture you are modeling.
       
       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvashr : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvashr"

(**
       Summary: \[ [ mk_rotate_left c i t1 ] \]
       Rotate bits of t1 to the left i times.
       
       The node t1 must have a bit-vector sort. 
    *)
external mk_rotate_left : context -> int -> ast -> ast
	= "camlidl_z3_Z3_mk_rotate_left"

(**
       Summary: \[ [ mk_rotate_right c i t1 ] \]
       Rotate bits of t1 to the right i times.
       
       The node t1 must have a bit-vector sort. 
    *)
external mk_rotate_right : context -> int -> ast -> ast
	= "camlidl_z3_Z3_mk_rotate_right"

(**
       Summary: \[ [ mk_ext_rotate_left c t1 t2 ] \]
       Rotate bits of t1 to the left t2 times.
       
       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_ext_rotate_left : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_ext_rotate_left"

(**
       Summary: \[ [ mk_ext_rotate_right c t1 t2 ] \]
       Rotate bits of t1 to the right t2 times.
       
       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_ext_rotate_right : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_ext_rotate_right"

(**
       Summary: \[ [ mk_int2bv c n t1 ] \]
       Create an n bit bit-vector from the integer argument t1.

       NB. This function is essentially treated as uninterpreted. 
       So you cannot expect Z3 to precisely reflect the semantics of this function
       when solving constraints with this function.
       
       The node t1 must have integer sort. 
    *)
external mk_int2bv : context -> int -> ast -> ast
	= "camlidl_z3_Z3_mk_int2bv"

(**
       Summary: \[ [ mk_bv2int c t1 is_signed ] \]
       Create an integer from the bit-vector argument t1.
       If is_signed is false, then the bit-vector t1 is treated as unsigned int. 
       So the result is non-negative
       and in the range {e [0..2^N-1] }, where N are the number of bits in t1.
       If is_signed is true, t1 is treated as a signed bit-vector.

       NB. This function is essentially treated as uninterpreted. 
       So you cannot expect Z3 to precisely reflect the semantics of this function
       when solving constraints with this function.

       The node t1 must have a bit-vector sort. 
    *)
external mk_bv2int : context -> ast -> bool -> ast
	= "camlidl_z3_Z3_mk_bv2int"

(**
       Summary: \[ [ mk_bvadd_no_overflow c t1 t2 is_signed ] \]
       Create a predicate that checks that the bit-wise addition
       of t1 and t2 does not overflow.
       
       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvadd_no_overflow : context -> ast -> ast -> bool -> ast
	= "camlidl_z3_Z3_mk_bvadd_no_overflow"

(**
       Summary: \[ [ mk_bvadd_no_underflow c t1 t2 ] \]
       Create a predicate that checks that the bit-wise signed addition
       of t1 and t2 does not underflow.
       
       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvadd_no_underflow : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvadd_no_underflow"

(**
       Summary: \[ [ mk_bvsub_no_overflow c t1 t2 ] \]
       Create a predicate that checks that the bit-wise signed subtraction
       of t1 and t2 does not overflow.
       
       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvsub_no_overflow : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsub_no_overflow"

(**
       Summary: \[ [ mk_bvsub_no_underflow c t1 t2 is_signed ] \]
       Create a predicate that checks that the bit-wise subtraction
       of t1 and t2 does not underflow.
       
       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvsub_no_underflow : context -> ast -> ast -> bool -> ast
	= "camlidl_z3_Z3_mk_bvsub_no_underflow"

(**
       Summary: \[ [ mk_bvsdiv_no_overflow c t1 t2 ] \]
       Create a predicate that checks that the bit-wise signed division 
       of t1 and t2 does not overflow.
       
       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvsdiv_no_overflow : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvsdiv_no_overflow"

(**
       Summary: \[ [ mk_bvneg_no_overflow c t1 ] \]
       Check that bit-wise negation does not overflow when 
       t1 is interpreted as a signed bit-vector.
       
       The node t1 must have bit-vector sort.
    *)
external mk_bvneg_no_overflow : context -> ast -> ast
	= "camlidl_z3_Z3_mk_bvneg_no_overflow"

(**
       Summary: \[ [ mk_bvmul_no_overflow c t1 t2 is_signed ] \]
       Create a predicate that checks that the bit-wise multiplication
       of t1 and t2 does not overflow.
       
       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvmul_no_overflow : context -> ast -> ast -> bool -> ast
	= "camlidl_z3_Z3_mk_bvmul_no_overflow"

(**
       Summary: \[ [ mk_bvmul_no_underflow c t1 t2 ] \]
       Create a predicate that checks that the bit-wise signed multiplication
       of t1 and t2 does not underflow.
       
       The nodes t1 and t2 must have the same bit-vector sort.
    *)
external mk_bvmul_no_underflow : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_bvmul_no_underflow"

(**
       Summary: \[ [ mk_select c a i ] \]
       Array read.

       The node a must have an array sort {e [domain -> range] }, and i must have the sort domain.
       The sort of the result is range.

       - {b See also}: {!Z3.mk_array_sort}
       - {b See also}: {!Z3.mk_store}
    *)
external mk_select : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_select"

(**
       Summary: \[ [ mk_store c a i v ] \]
       Array update.
       
       The node a must have an array sort {e [domain -> range] }, i must have sort domain,
       v must have sort range. The sort of the result is {e [domain -> range] }.
       
       - {b See also}: {!Z3.mk_array_sort}
       - {b See also}: {!Z3.mk_select}
    *)
external mk_store : context -> ast -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_store"

(** 
        Summary: Create the constant array.

        
        
        
    *)
external mk_const_array : context -> sort -> ast -> ast
	= "camlidl_z3_Z3_mk_const_array"

(**
       Summary: \[ [ mk_map f n args ] \]
       map f on the the argument arrays.
       
       The n nodes args must be of array sorts {e [domain_i -> range_i] }.
       The function declaration f must have type {e  range_1 .. range_n -> range }.
       v must have sort range. The sort of the result is {e [domain_i -> range] }.
       
       - {b See also}: {!Z3.mk_array_sort}
       - {b See also}: {!Z3.mk_store}
       - {b See also}: {!Z3.mk_select}
    *)
external mk_map : context -> func_decl -> int -> ast -> ast
	= "camlidl_z3_Z3_mk_map"

(** 
        Summary: Access the array default value.
        Produces the default range value, for arrays that can be represented as 
        finite maps with a default range value.

        
        

    *)
external mk_array_default : context -> ast -> ast
	= "camlidl_z3_Z3_mk_array_default"

(**
       {2 {L Sets}}
    *)
(**
       Summary: Create Set type.
    *)
external mk_set_sort : context -> sort -> sort
	= "camlidl_z3_Z3_mk_set_sort"

(** 
        Summary: Create the empty set.
    *)
external mk_empty_set : context -> sort -> ast
	= "camlidl_z3_Z3_mk_empty_set"

(** 
        Summary: Create the full set.
    *)
external mk_full_set : context -> sort -> ast
	= "camlidl_z3_Z3_mk_full_set"

(**
       Summary: Add an element to a set.
       
       The first argument must be a set, the second an element.
    *)
external mk_set_add : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_set_add"

(**
       Summary: Remove an element to a set.
       
       The first argument must be a set, the second an element.
    *)
external mk_set_del : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_set_del"

(**
       Summary: Take the union of a list of sets.
    *)
external mk_set_union : context -> ast array -> ast
	= "camlidl_z3_Z3_mk_set_union"

(**
       Summary: Take the intersection of a list of sets.
    *)
external mk_set_intersect : context -> ast array -> ast
	= "camlidl_z3_Z3_mk_set_intersect"

(**
       Summary: Take the set difference between two sets.
    *)
external mk_set_difference : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_set_difference"

(**
       Summary: Take the complement of a set.
    *)
external mk_set_complement : context -> ast -> ast
	= "camlidl_z3_Z3_mk_set_complement"

(**
       Summary: Check for set membership.
       
       The first argument should be an element type of the set.
    *)
external mk_set_member : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_set_member"

(**
       Summary: Check for subsetness of sets.
    *)
external mk_set_subset : context -> ast -> ast -> ast
	= "camlidl_z3_Z3_mk_set_subset"

(**
       {2 {L Numerals}}
    *)
(**
       Summary: Create a numeral of a given sort. 

       
       
       
       
       - {b See also}: {!Z3.mk_int}
       - {b See also}: {!Z3.mk_unsigned_int}
    *)
external mk_numeral : context -> string -> sort -> ast
	= "camlidl_z3_Z3_mk_numeral"

(**
       Summary: Create a real from a fraction.

       
       
       

       - {b Precondition}: den != 0

       - {b See also}: {!Z3.mk_numeral}
       - {b See also}: {!Z3.mk_int}
       - {b See also}: {!Z3.mk_unsigned_int}
    *)
external mk_real : context -> int -> int -> ast
	= "camlidl_z3_Z3_mk_real"

(**
       Summary: Create a numeral of a given sort. 
       
       This function can be use to create numerals that fit in a machine integer.
       It is slightly faster than {!Z3.mk_numeral} since it is not necessary to parse a string.

       - {b See also}: {!Z3.mk_numeral}
    *)
external mk_int : context -> int -> sort -> ast
	= "camlidl_z3_Z3_mk_int"

(**
       Summary: Create a numeral of a given sort. 
       
       This function can be use to create numerals that fit in a machine unsinged integer.
       It is slightly faster than {!Z3.mk_numeral} since it is not necessary to parse a string.

       - {b See also}: {!Z3.mk_numeral}
    *)
external mk_unsigned_int : context -> int -> sort -> ast
	= "camlidl_z3_Z3_mk_unsigned_int"

(**
       {2 {L Quantifiers}}
    *)
(**
       Summary: Create a pattern for quantifier instantiation.

       Z3 uses pattern matching to instantiate quantifiers. If a
       pattern is not provided for a quantifier, then Z3 will
       automatically compute a set of patterns for it. However, for
       optimal performance, the user should provide the patterns.

       Patterns comprise a list of terms. The list should be
       non-empty.  If the list comprises of more than one term, it is
       a called a multi-pattern.
       
       In general, one can pass in a list of (multi-)patterns in the
       quantifier constructor.


       - {b See also}: {!Z3.mk_forall}
       - {b See also}: {!Z3.mk_exists}
    *)
external mk_pattern : context -> ast array -> pattern
	= "camlidl_z3_Z3_mk_pattern"

(**
       Summary: Create a bound variable.

       Bound variables are indexed by de-Bruijn indices. It is perhaps easiest to explain
       the meaning of de-Bruijn indices by indicating the compilation process from
       non-de-Bruijn formulas to de-Bruijn format.

       {v  
       abs(forall (x1) phi) = forall (x1) abs1(phi, x1, 0)
       abs(forall (x1, x2) phi) = abs(forall (x1) abs(forall (x2) phi))
       abs1(x, x, n) = b_n
       abs1(y, x, n) = y
       abs1(f(t1,...,tn), x, n) = f(abs1(t1,x,n), ..., abs1(tn,x,n))
       abs1(forall (x1) phi, x, n) = forall (x1) (abs1(phi, x, n+1))
        v}

       The last line is significant: the index of a bound variable is different depending
       on the scope in which it appears. The deeper x appears, the higher is its
       index.
       
       
       
       

       - {b See also}: {!Z3.mk_forall}
       - {b See also}: {!Z3.mk_exists}
    *)
external mk_bound : context -> int -> sort -> ast
	= "camlidl_z3_Z3_mk_bound"

(**
       Summary: Create a forall formula.

        [mk_forall c w p t n b] creates a forall formula, where
       [w] is the weight, [p] is an array of patterns, [t] is an array
       with the sorts of the bound variables, [n] is an array with the
       'names' of the bound variables, and [b] is the body of the
       quantifier. Quantifiers are associated with weights indicating
       the importance of using the quantifier during
       instantiation. 
       
       
       
       
       
       
       
       
       
       
       - {b See also}: {!Z3.mk_pattern}
       - {b See also}: {!Z3.mk_bound}
       - {b See also}: {!Z3.mk_exists}
    *)
external mk_forall : context -> int -> pattern array -> sort array -> symbol array -> ast -> ast
	= "camlidl_z3_Z3_mk_forall_bytecode" "camlidl_z3_Z3_mk_forall"

(**
       Summary: Create an exists formula. Similar to {!Z3.mk_forall}.
       
       - {b See also}: {!Z3.mk_pattern}
       - {b See also}: {!Z3.mk_bound}
       - {b See also}: {!Z3.mk_forall}
    *)
external mk_exists : context -> int -> pattern array -> sort array -> symbol array -> ast -> ast
	= "camlidl_z3_Z3_mk_exists_bytecode" "camlidl_z3_Z3_mk_exists"

(**
       Summary: Create a quantifier - universal or existential, with pattern hints.
       
       
       
       
       
       
       
       
       
       
       
       - {b See also}: {!Z3.mk_pattern}
       - {b See also}: {!Z3.mk_bound}
       - {b See also}: {!Z3.mk_forall}
       - {b See also}: {!Z3.mk_exists}
    *)
external mk_quantifier : context -> bool -> int -> pattern array -> sort array -> symbol array -> ast -> ast
	= "camlidl_z3_Z3_mk_quantifier_bytecode" "camlidl_z3_Z3_mk_quantifier"

(**
       Summary: Create a quantifier - universal or existential, with pattern hints, no patterns, and attributes
       
       
       
       
       
       
       
       
       
       
       
       
       
       
       
       - {b See also}: {!Z3.mk_pattern}
       - {b See also}: {!Z3.mk_bound}
       - {b See also}: {!Z3.mk_forall}
       - {b See also}: {!Z3.mk_exists}
    *)
external mk_quantifier_ex : context -> bool -> int -> symbol -> symbol -> pattern array -> ast array -> sort array -> symbol array -> ast -> ast
	= "camlidl_z3_Z3_mk_quantifier_ex_bytecode" "camlidl_z3_Z3_mk_quantifier_ex"

(**
       Summary: Create a universal quantifier using a list of constants that
       will form the set of bound variables.

       
       
              the quantifier during instantiation. By default, pass the weight 0.
       
       
       
       
       
       
       - {b See also}: {!Z3.mk_pattern}
       - {b See also}: {!Z3.mk_exists_const}

    *)
external mk_forall_const : context -> int -> app array -> pattern array -> ast -> ast
	= "camlidl_z3_Z3_mk_forall_const"

(**
       Summary: Similar to {!Z3.mk_forall_const}.

       Summary: Create an existential quantifier using a list of constants that
       will form the set of bound variables.

       
       
              the quantifier during instantiation. By default, pass the weight 0.
       
       
       
       
       
       
       - {b See also}: {!Z3.mk_pattern}
       - {b See also}: {!Z3.mk_forall_const}
    *)
external mk_exists_const : context -> int -> app array -> pattern array -> ast -> ast
	= "camlidl_z3_Z3_mk_exists_const"

(**
       Summary: Create a universal or existential 
       quantifier using a list of constants that
       will form the set of bound variables.
    *)
external mk_quantifier_const : context -> bool -> int -> app array -> pattern array -> ast -> ast
	= "camlidl_z3_Z3_mk_quantifier_const_bytecode" "camlidl_z3_Z3_mk_quantifier_const"

(**
       Summary: Create a universal or existential 
       quantifier using a list of constants that
       will form the set of bound variables.
    *)
external mk_quantifier_const_ex : context -> bool -> int -> symbol -> symbol -> app array -> pattern array -> ast array -> ast -> ast
	= "camlidl_z3_Z3_mk_quantifier_const_ex_bytecode" "camlidl_z3_Z3_mk_quantifier_const_ex"

(**
       {2 {L Accessors}}
    *)
(** 
        Summary: Return a unique identifier for t.
    *)
external get_ast_id : context -> ast -> int
	= "camlidl_z3_Z3_get_ast_id"

(** 
        Summary: Return a unique identifier for f.
    *)
external get_func_decl_id : context -> func_decl -> int
	= "camlidl_z3_Z3_get_func_decl_id"

(** 
        Summary: Return a unique identifier for s.
    *)
external get_sort_id : context -> sort -> int
	= "camlidl_z3_Z3_get_sort_id"

(**
       Summary: Return true if the given expression t is well sorted.
    *)
external is_well_sorted : context -> ast -> bool
	= "camlidl_z3_Z3_is_well_sorted"

(**
       Summary: Return INT_SYMBOL if the symbol was constructed
       using {!Z3.mk_int_symbol}, and STRING_SYMBOL if the symbol
       was constructed using {!Z3.mk_string_symbol}.
    *)
external get_symbol_kind : context -> symbol -> symbol_kind
	= "camlidl_z3_Z3_get_symbol_kind"

(**
       Summary: \[ [ get_symbol_int c s ] \]
       Return the symbol int value. 
       
       - {b Precondition}: get_symbol_kind s == INT_SYMBOL

       - {b See also}: {!Z3.mk_int_symbol}
    *)
external get_symbol_int : context -> symbol -> int
	= "camlidl_z3_Z3_get_symbol_int"

(**
       Summary: \[ [ get_symbol_string c s ] \]
       Return the symbol name. 

       - {b Precondition}: get_symbol_string s == STRING_SYMBOL

       
       
       

       - {b See also}: {!Z3.mk_string_symbol}
    *)
external get_symbol_string : context -> symbol -> string
	= "camlidl_z3_Z3_get_symbol_string"

(**
       Summary: Return the kind of the given AST.
    *)
external get_ast_kind : context -> ast -> ast_kind
	= "camlidl_z3_Z3_get_ast_kind"

(**
       Summary: Return numeral value, as a string of a numeric constant term

       - {b Precondition}: get_ast_kind c a == NUMERAL_AST
    *)
external get_numeral_string : context -> ast -> string
	= "camlidl_z3_Z3_get_numeral_string"

(**
       Summary: Return numeral value, as a pair of 64 bit numbers if the representation fits.

       
       
       
       
       
       Preturn TRUE if the numeral value fits in 64 bit numerals, FALSE otherwise.

       - {b Precondition}: get_ast_kind a == NUMERAL_AST
    *)
external get_numeral_small : context -> ast -> bool * int64 * int64
	= "camlidl_z3_Z3_get_numeral_small"

(**
       Summary: \[ [ get_numeral_int c v ] \]
       Similar to {!Z3.get_numeral_string}, but only succeeds if
       the value can fit in a machine int. Return TRUE if the call succeeded.

       - {b Precondition}: get_ast_kind c v == NUMERAL_AST
      
       - {b See also}: {!Z3.get_numeral_string}
    *)
external get_numeral_int : context -> ast -> bool * int
	= "camlidl_z3_Z3_get_numeral_int"

(**
       Summary: \[ [ get_numeral_uint c v ] \]
       Similar to {!Z3.get_numeral_string}, but only succeeds if
       the value can fit in a machine unsigned int int. Return TRUE if the call succeeded.

       - {b Precondition}: get_ast_kind c v == NUMERAL_AST
      
       - {b See also}: {!Z3.get_numeral_string}
    *)
external get_numeral_uint : context -> ast -> bool * int
	= "camlidl_z3_Z3_get_numeral_uint"

(**
       Summary: Return L_TRUE if a is true, L_FALSE if it is false, and L_UNDEF otherwise.
    *)
external get_bool_value : context -> ast -> lbool
	= "camlidl_z3_Z3_get_bool_value"

(**
       Summary: Return the declaration of a constant or function application.
    *)
external get_app_decl : context -> app -> func_decl
	= "camlidl_z3_Z3_get_app_decl"

(**
       Summary: \[ [ get_app_num_args c a ] \]
       Return the number of argument of an application. If t
       is an constant, then the number of arguments is 0.
    *)
external get_app_num_args : context -> app -> int
	= "camlidl_z3_Z3_get_app_num_args"

(**
       Summary: \[ [ get_app_arg c a i ] \]
       Return the i-th argument of the given application.
       
       - {b Precondition}: i < get_num_args c a
    *)
external get_app_arg : context -> app -> int -> ast
	= "camlidl_z3_Z3_get_app_arg"

(**
       Summary: Return index of de-Brujin bound variable.

       - {b Precondition}: get_ast_kind a == VAR_AST
    *)
external get_index_value : context -> ast -> int
	= "camlidl_z3_Z3_get_index_value"

(**
       Summary: Determine if quantifier is universal.
       
       - {b Precondition}: get_ast_kind a == QUANTIFIER_AST
    *)
external is_quantifier_forall : context -> ast -> bool
	= "camlidl_z3_Z3_is_quantifier_forall"

(**
       Summary: Obtain weight of quantifier.
       
       - {b Precondition}: get_ast_kind a == QUANTIFIER_AST
    *)
external get_quantifier_weight : context -> ast -> int
	= "camlidl_z3_Z3_get_quantifier_weight"

(**
       Summary: Return number of patterns used in quantifier.
       
       - {b Precondition}: get_ast_kind a == QUANTIFIER_AST
    *)
external get_quantifier_num_patterns : context -> ast -> int
	= "camlidl_z3_Z3_get_quantifier_num_patterns"

(**
       Summary: Return i'th pattern.
       
       - {b Precondition}: get_ast_kind a == QUANTIFIER_AST
    *)
external get_quantifier_pattern_ast : context -> ast -> int -> pattern
	= "camlidl_z3_Z3_get_quantifier_pattern_ast"

(**
       Summary: Return number of no_patterns used in quantifier.
       
       - {b Precondition}: get_ast_kind a == QUANTIFIER_AST
    *)
external get_quantifier_num_no_patterns : context -> ast -> int
	= "camlidl_z3_Z3_get_quantifier_num_no_patterns"

(**
       Summary: Return i'th no_pattern.
       
       - {b Precondition}: get_ast_kind a == QUANTIFIER_AST
    *)
external get_quantifier_no_pattern_ast : context -> ast -> int -> ast
	= "camlidl_z3_Z3_get_quantifier_no_pattern_ast"

(**
       Summary: Return symbol of the i'th bound variable.
       
       - {b Precondition}: get_ast_kind a == QUANTIFIER_AST
    *)
external get_quantifier_bound_name : context -> ast -> int -> symbol
	= "camlidl_z3_Z3_get_quantifier_bound_name"

(**
       Summary: Return sort of the i'th bound variable.
       
       - {b Precondition}: get_ast_kind a == QUANTIFIER_AST
    *)
external get_quantifier_bound_sort : context -> ast -> int -> sort
	= "camlidl_z3_Z3_get_quantifier_bound_sort"

(**
       Summary: Return body of quantifier.
       
       - {b Precondition}: get_ast_kind a == QUANTIFIER_AST
    *)
external get_quantifier_body : context -> ast -> ast
	= "camlidl_z3_Z3_get_quantifier_body"

(**
       Summary: Return number of bound variables of quantifier.
       
       - {b Precondition}: get_ast_kind a == QUANTIFIER_AST
    *)
external get_quantifier_num_bound : context -> ast -> int
	= "camlidl_z3_Z3_get_quantifier_num_bound"

(**
       Summary: Return the constant declaration name as a symbol. 
    *)
external get_decl_name : context -> func_decl -> symbol
	= "camlidl_z3_Z3_get_decl_name"

(**
       Summary: Return the number of parameters associated with a declaration.
    *)
external get_decl_num_parameters : context -> func_decl -> int
	= "camlidl_z3_Z3_get_decl_num_parameters"

(**
       Summary: Return the parameter type associated with a declaration.
       
       
       
       
    *)
external get_decl_parameter_kind : context -> func_decl -> int -> parameter_kind
	= "camlidl_z3_Z3_get_decl_parameter_kind"

(**
       Summary: Return the integer value associated with an integer parameter.

       - {b Precondition}: get_decl_parameter_kind c d idx == PARAMETER_INT
    *)
external get_decl_int_parameter : context -> func_decl -> int -> int
	= "camlidl_z3_Z3_get_decl_int_parameter"

(**
       Summary: Return the double value associated with an double parameter.

       - {b Precondition}: get_decl_parameter_kind c d idx == PARAMETER_DOUBLE
    *)
external get_decl_double_parameter : context -> func_decl -> int -> float
	= "camlidl_z3_Z3_get_decl_double_parameter"

(**
       Summary: Return the double value associated with an double parameter.

       - {b Precondition}: get_decl_parameter_kind c d idx == PARAMETER_SYMBOL
    *)
external get_decl_symbol_parameter : context -> func_decl -> int -> symbol
	= "camlidl_z3_Z3_get_decl_symbol_parameter"

(**
       Summary: Return the sort value associated with a sort parameter.

       - {b Precondition}: get_decl_parameter_kind c d idx == PARAMETER_SORT
    *)
external get_decl_sort_parameter : context -> func_decl -> int -> sort
	= "camlidl_z3_Z3_get_decl_sort_parameter"

(**
       Summary: Return the expresson value associated with an expression parameter.

       - {b Precondition}: get_decl_parameter_kind c d idx == PARAMETER_AST
    *)
external get_decl_ast_parameter : context -> func_decl -> int -> ast
	= "camlidl_z3_Z3_get_decl_ast_parameter"

(**
       Summary: Return the expresson value associated with an expression parameter.

       - {b Precondition}: get_decl_parameter_kind c d idx == PARAMETER_FUNC_DECL
    *)
external get_decl_func_decl_parameter : context -> func_decl -> int -> func_decl
	= "camlidl_z3_Z3_get_decl_func_decl_parameter"

(**
       Summary: Return the rational value, as a string, associated with a rational parameter.

       - {b Precondition}: get_decl_parameter_kind c d idx == PARAMETER_RATIONAL
    *)
external get_decl_rational_parameter : context -> func_decl -> int -> string
	= "camlidl_z3_Z3_get_decl_rational_parameter"

(**
       Summary: Return the sort name as a symbol. 
    *)
external get_sort_name : context -> sort -> symbol
	= "camlidl_z3_Z3_get_sort_name"

(**
       Summary: Return the sort of an AST node.
       
       The AST node must be a constant, application, numeral, bound variable, or quantifier.

    *)
external get_sort : context -> ast -> sort
	= "camlidl_z3_Z3_get_sort"

(**
       Summary: Return the number of parameters of the given declaration.

       - {b See also}: {!Z3.get_domain_size}
    *)
external get_domain_size : context -> func_decl -> int
	= "camlidl_z3_Z3_get_domain_size"

(**
       Summary: \[ [ get_domain c d i ] \]
       Return the sort of the i-th parameter of the given function declaration.
       
       - {b Precondition}: i < get_domain_size d

       - {b See also}: {!Z3.get_domain_size}
    *)
external get_domain : context -> func_decl -> int -> sort
	= "camlidl_z3_Z3_get_domain"

(**
       Summary: \[ [ get_range c d ] \]
       Return the range of the given declaration. 

       If d is a constant (i.e., has zero arguments), then this
       function returns the sort of the constant.
    *)
external get_range : context -> func_decl -> sort
	= "camlidl_z3_Z3_get_range"

(**
       Summary: Return the sort kind (e.g., array, tuple, int, bool, etc).

       - {b See also}: {!Z3.sort_kind}
    *)
external get_sort_kind : context -> sort -> sort_kind
	= "camlidl_z3_Z3_get_sort_kind"

(**
       Summary: \[ [ get_bv_sort_size c t ] \]
       Return the size of the given bit-vector sort. 

       - {b Precondition}: get_sort_kind c t == BV_SORT

       - {b See also}: {!Z3.mk_bv_sort}
       - {b See also}: {!Z3.get_sort_kind}
    *)
external get_bv_sort_size : context -> sort -> int
	= "camlidl_z3_Z3_get_bv_sort_size"

(**
       Summary: \[ [ get_array_sort_domain c t ] \]
       Return the domain of the given array sort.
       
       - {b Precondition}: get_sort_kind c t == ARRAY_SORT

       - {b See also}: {!Z3.mk_array_sort}
       - {b See also}: {!Z3.get_sort_kind}
    *)
external get_array_sort_domain : context -> sort -> sort
	= "camlidl_z3_Z3_get_array_sort_domain"

(**
       Summary: \[ [ get_array_sort_range c t ] \] 
       Return the range of the given array sort. 

       - {b Precondition}: get_sort_kind c t == ARRAY_SORT

       - {b See also}: {!Z3.mk_array_sort}
       - {b See also}: {!Z3.get_sort_kind}
    *)
external get_array_sort_range : context -> sort -> sort
	= "camlidl_z3_Z3_get_array_sort_range"

(**
       Summary: \[ [ get_tuple_sort_mk_decl c t ] \]
       Return the constructor declaration of the given tuple
       sort. 

       - {b Precondition}: get_sort_kind c t == DATATYPE_SORT

       - {b See also}: {!Z3.mk_tuple_sort}
       - {b See also}: {!Z3.get_sort_kind}
    *)
external get_tuple_sort_mk_decl : context -> sort -> func_decl
	= "camlidl_z3_Z3_get_tuple_sort_mk_decl"

(**
       Summary: Return declaration kind corresponding to declaration.
    *)
external get_decl_kind : context -> func_decl -> decl_kind
	= "camlidl_z3_Z3_get_decl_kind"

(**
       Summary: \[ [ get_tuple_sort_num_fields c t ] \]
       Return the number of fields of the given tuple sort. 

       - {b Precondition}: get_sort_kind c t == DATATYPE_SORT

        - {b Remarks}: Consider using the function {!Z3.get_tuple_sort}, which 
       returns a tuple: tuple constructor, and an array of the tuple sort fields. 

       - {b See also}: {!Z3.mk_tuple_sort}
       - {b See also}: {!Z3.get_sort_kind}
    *)
external get_tuple_sort_num_fields : context -> sort -> int
	= "camlidl_z3_Z3_get_tuple_sort_num_fields"

(**
       Summary: \[ [ get_tuple_sort_field_decl c t i ] \]
       Return the i-th field declaration (i.e., projection function declaration)
       of the given tuple sort. 

        - {b Remarks}: Consider using the function {!Z3.get_tuple_sort}, which 
       returns a tuple: tuple constructor, and an array of the tuple sort fields. 

       - {b Precondition}: get_sort_kind t == DATATYPE_SORT
       - {b Precondition}: i < get_tuple_sort_num_fields c t
       
       - {b See also}: {!Z3.mk_tuple_sort}
       - {b See also}: {!Z3.get_sort_kind}
    *)
external get_tuple_sort_field_decl : context -> sort -> int -> func_decl
	= "camlidl_z3_Z3_get_tuple_sort_field_decl"

(** 
        Summary: Return number of constructors for datatype.

        - {b Precondition}: get_sort_kind t == DATATYPE_SORT

        - {b See also}: {!Z3.get_datatype_sort_constructor}
        - {b See also}: {!Z3.get_datatype_sort_recognizer}
        - {b See also}: {!Z3.get_datatype_sort_constructor_accessor}

    *)
external get_datatype_sort_num_constructors : context -> sort -> int
	= "camlidl_z3_Z3_get_datatype_sort_num_constructors"

(** 
        Summary: Return idx'th constructor.

        - {b Precondition}: get_sort_kind t == DATATYPE_SORT
        - {b Precondition}: idx < get_datatype_sort_num_constructors c t

        - {b See also}: {!Z3.get_datatype_sort_num_constructors}
        - {b See also}: {!Z3.get_datatype_sort_recognizer}
        - {b See also}: {!Z3.get_datatype_sort_constructor_accessor}

    *)
external get_datatype_sort_constructor : context -> sort -> int -> func_decl
	= "camlidl_z3_Z3_get_datatype_sort_constructor"

(** 
        Summary: Return idx'th recognizer.

        - {b Precondition}: get_sort_kind t == DATATYPE_SORT
        - {b Precondition}: idx < get_datatype_sort_num_constructors c t

        - {b See also}: {!Z3.get_datatype_sort_num_constructors}
        - {b See also}: {!Z3.get_datatype_sort_constructor}
        - {b See also}: {!Z3.get_datatype_sort_constructor_accessor}

    *)
external get_datatype_sort_recognizer : context -> sort -> int -> func_decl
	= "camlidl_z3_Z3_get_datatype_sort_recognizer"

(** 
        Summary: Return idx_a'th accessor for the idx_c'th constructor.

        - {b Precondition}: get_sort_kind t == DATATYPE_SORT
        - {b Precondition}: idx_c < get_datatype_sort_num_constructors c t
        - {b Precondition}: idx_a < get_domain_size c get_datatype_sort_constructor c idx_c

        - {b See also}: {!Z3.get_datatype_sort_num_constructors}
        - {b See also}: {!Z3.get_datatype_sort_constructor}
        - {b See also}: {!Z3.get_datatype_sort_recognizer}
    *)
external get_datatype_sort_constructor_accessor : context -> sort -> int -> int -> func_decl
	= "camlidl_z3_Z3_get_datatype_sort_constructor_accessor"

(** 
        Summary: Return arity of relation.

        - {b Precondition}: get_sort_kind s == RELATION_SORT

        - {b See also}: {!Z3.get_relation_column}
    *)
external get_relation_arity : context -> sort -> int
	= "camlidl_z3_Z3_get_relation_arity"

(** 
        Summary: Return sort at i'th column of relation sort.

        - {b Precondition}: get_sort_kind c s == RELATION_SORT
        - {b Precondition}: col < get_relation_arity c s

        - {b See also}: {!Z3.get_relation_arity}
    *)
external get_relation_column : context -> sort -> int -> sort
	= "camlidl_z3_Z3_get_relation_column"

(** 
        Summary: Return number of terms in pattern.
    *)
external get_pattern_num_terms : context -> pattern -> int
	= "camlidl_z3_Z3_get_pattern_num_terms"

(**
       Summary: Return i'th ast in pattern.
    *)
external get_pattern : context -> pattern -> int -> ast
	= "camlidl_z3_Z3_get_pattern"

(** 
        Summary: Interface to simplifier.

        Provides an interface to the AST simplifier used by Z3.
        It allows clients to piggyback on top of the AST simplifier
        for their own term manipulation.
    *)
external simplify : context -> ast -> ast
	= "camlidl_z3_Z3_simplify"

(**
       {2 {L Modifiers}}
    *)
(**
       Summary: Update the arguments of term a using the arguments args.
       The number of arguments num_args should coincide 
       with the number of arguments to a.
       If a is a quantifier, then num_args has to be 1.
    *)
external update_term : context -> ast -> ast array -> ast
	= "camlidl_z3_Z3_update_term"

(**
       Summary: Substitute every occurrence of {e from[i] } in a with {e to[i] }, for i smaller than num_exprs.
       The result is the new AST. The arrays from and to must have size num_exprs.
       For every i smaller than num_exprs, we must have that sort of {e from[i] } must be equal to sort of {e to[i] }.
    *)
external substitute : context -> ast -> ast array -> ast array -> ast
	= "camlidl_z3_Z3_substitute"

(**
       Summary: Substitute the free variables in a with the expressions in to.
       For every i smaller than num_exprs, the variable with de-Bruijn index i is replaced with term {e to[i] }.
    *)
external substitute_vars : context -> ast -> ast array -> ast
	= "camlidl_z3_Z3_substitute_vars"

(**
       {2 {L Coercions}}
    *)
(**
       Summary: Convert a sort into ast. This is just type casting.
    *)
external sort_to_ast : context -> sort -> ast
	= "camlidl_z3_Z3_sort_to_ast"

(**
       Summary: Convert a func_decl into ast. This is just type casting.
    *)
external func_decl_to_ast : context -> func_decl -> ast
	= "camlidl_z3_Z3_func_decl_to_ast"

(**
       Summary: Convert a pattern into ast. This is just type casting.
    *)
external pattern_to_ast : context -> pattern -> ast
	= "camlidl_z3_Z3_pattern_to_ast"

(**
       Summary: Convert a APP_AST into an AST. This is just type casting.
    *)
external app_to_ast : context -> app -> ast
	= "camlidl_z3_Z3_app_to_ast"

(**
       Summary: Convert an AST into a APP_AST. This is just type casting.
       
       - {b Warning}: This conversion is only safe if {!Z3.get_ast_kind} returns app.
    *)
external to_app : context -> ast -> app
	= "camlidl_z3_Z3_to_app"

(**
       {2 {L Constraints}}
    *)
(** 
        Summary: Create a backtracking point.
        
        The logical context can be viewed as a stack of contexts.  The
        scope level is the number of elements on this stack. The stack
        of contexts is simulated using trail (undo) stacks.

        - {b See also}: {!Z3.pop}
    *)
external push : context -> unit
	= "camlidl_z3_Z3_push"

(**
       Summary: Backtrack.
       
       Restores the context from the top of the stack, and pops it off the
       stack.  Any changes to the logical context (by {!Z3.assert_cnstr} or
       other functions) between the matching {!Z3.push} and pop
       operators are flushed, and the context is completely restored to
       what it was right before the {!Z3.push}.
       
       - {b See also}: {!Z3.push}
    *)
external pop : context -> int -> unit
	= "camlidl_z3_Z3_pop"

(**
       Summary: Retrieve the current scope level.
       
       It retrieves the number of scopes that have been pushed, but not yet popped.
       
       - {b See also}: {!Z3.push}
       - {b See also}: {!Z3.pop}
    *)
external get_num_scopes : context -> int
	= "camlidl_z3_Z3_get_num_scopes"

(**
       Summary: Persist AST through num_scopes pops.
       This function is only relevant if c was created using {!Z3.mk_context}.
       If c was created using {!Z3.mk_context_rc}, this function is a NOOP.
       
       Normally, for contexts created using {!Z3.mk_context}, 
       references to terms are no longer valid when 
       popping scopes beyond the level where the terms are created.
       If you want to reference a term below the scope where it
       was created, use this method to specify how many pops
       the term should survive.
       The num_scopes should be at most equal to the number of
       calls to push subtracted with the calls to pop.
    *)
external persist_ast : context -> ast -> int -> unit
	= "camlidl_z3_Z3_persist_ast"

(**
       Summary: Assert a constraing into the logical context.
       
       After one assertion, the logical context may become
       inconsistent.  
       
       The functions {!Z3.check} or {!Z3.check_and_get_model} should be
       used to check whether the logical context is consistent or not.

       - {b See also}: {!Z3.check}
       - {b See also}: {!Z3.check_and_get_model}
    *)
external assert_cnstr : context -> ast -> unit
	= "camlidl_z3_Z3_assert_cnstr"

(**
       Summary: Check whether the given logical context is consistent or not.

       If the logical context is not unsatisfiable (i.e., the return value is different from L_FALSE)
       and model construction is enabled (see {!Z3.mk_config}), then a model is stored in m. Otherwise,
       the value 0 is stored in m.
       The caller is responsible for deleting the model using the function {!Z3.del_model}.
       
       - {b Remarks}: Model construction must be enabled using configuration
       parameters (See, {!Z3.mk_config}).

       - {b See also}: {!Z3.check}
       - {b See also}: {!Z3.del_model}
    *)
external check_and_get_model : context -> lbool * model
	= "camlidl_z3_Z3_check_and_get_model"

(**
       Summary: Check whether the given logical context is consistent or not.

       The function {!Z3.check_and_get_model} should be used when models are needed.

       - {b See also}: {!Z3.check_and_get_model}
    *)
external check : context -> lbool
	= "camlidl_z3_Z3_check"

(**
       Summary: Check whether the given logical context and optional assumptions is consistent or not.

       If the logical context is not unsatisfiable (i.e., the return value is different from L_FALSE),
       a non-0 model argument is passed in,
       and model construction is enabled (see {!Z3.mk_config}), then a model is stored in m. 
       Otherwise, m is left unchanged.
       The caller is responsible for deleting the model using the function {!Z3.del_model}.
       
       - {b Remarks}: If the model argument is non-0, then model construction must be enabled using configuration
       parameters (See, {!Z3.mk_config}).

       
       
       
       
       
       
       
              The unsatisfiable core is a subset of the assumptions, so the array has the same size as the assumptions.
              The core array is not populated if core_size is set to 0.

       - {b Precondition}: assumptions comprises of propositional literals.
            In other words, you cannot use compound formulas for assumptions, 
            but should use propositional variables or negations of propositional variables.
              
       - {b See also}: {!Z3.check}
       - {b See also}: {!Z3.del_model}
    *)
external check_assumptions : context -> ast array -> int -> ast array -> lbool * model * ast * int * ast array
	= "camlidl_z3_Z3_check_assumptions"

(**
       Summary: Retrieve congruence class representatives for terms.

       The function can be used for relying on Z3 to identify equal terms under the current
       set of assumptions. The array of terms and array of class identifiers should have
       the same length. The class identifiers are numerals that are assigned to the same
       value for their corresponding terms if the current context forces the terms to be
       equal. You cannot deduce that terms corresponding to different numerals must be all different, 
       (especially when using non-convex theories).
       All implied equalities are returned by this call.
       This means that two terms map to the same class identifier if and only if
       the current context implies that they are equal.

       A side-effect of the function is a satisfiability check.
       The function return L_FALSE if the current assertions are not satisfiable.

       - {b See also}: {!Z3.check_and_get_model}
       - {b See also}: {!Z3.check}
    *)
external get_implied_equalities : context -> ast array -> lbool * int array
	= "camlidl_z3_Z3_get_implied_equalities"

(**
       Summary: Delete a model object.
       
       - {b See also}: {!Z3.check_and_get_model}
    *)
external del_model : context -> model -> unit
	= "camlidl_z3_Z3_del_model"

(**
       {2 {L Search control.}}
    *)
(**
       Summary: Cancel an ongoing check.
       
       Notifies the current check to abort and return.
       This method should be called from a different thread
       than the one performing the check.
    *)
external soft_check_cancel : context -> unit
	= "camlidl_z3_Z3_soft_check_cancel"

(**
       Summary: Retrieve reason for search failure.
       
       If a call to {!Z3.check} or {!Z3.check_and_get_model} returns L_UNDEF, 
       use this facility to determine the more detailed cause of search failure.
    *)
external get_search_failure : context -> search_failure
	= "camlidl_z3_Z3_get_search_failure"

(**
       {2 {L Labels.}}
    *)
(** 
        Summary: Retrieve the set of labels that were relevant in
        the context of the current satisfied context.

        - {b See also}: {!Z3.del_literals}
        - {b See also}: {!Z3.get_num_literals}
        - {b See also}: {!Z3.get_label_symbol}
        - {b See also}: {!Z3.get_literal}
    *)
external get_relevant_labels : context -> literals
	= "camlidl_z3_Z3_get_relevant_labels"

(** 
        Summary: Retrieve the set of literals that satisfy the current context.

        - {b See also}: {!Z3.del_literals}
        - {b See also}: {!Z3.get_num_literals}
        - {b See also}: {!Z3.get_label_symbol}
        - {b See also}: {!Z3.get_literal}
    *)
external get_relevant_literals : context -> literals
	= "camlidl_z3_Z3_get_relevant_literals"

(** 
        Summary: Retrieve the set of literals that whose assignment were 
        guess, but not propagated during the search.

        - {b See also}: {!Z3.del_literals}
        - {b See also}: {!Z3.get_num_literals}
        - {b See also}: {!Z3.get_label_symbol}
        - {b See also}: {!Z3.get_literal}
    *)
external get_guessed_literals : context -> literals
	= "camlidl_z3_Z3_get_guessed_literals"

(**
       Summary: Delete a labels context.
       
       - {b See also}: {!Z3.get_relevant_labels}
    *)
external del_literals : context -> literals -> unit
	= "camlidl_z3_Z3_del_literals"

(**
       Summary: Retrieve the number of label symbols that were returned.
       
       - {b See also}: {!Z3.get_relevant_labels}
    *)
external get_num_literals : context -> literals -> int
	= "camlidl_z3_Z3_get_num_literals"

(**
       Summary: Retrieve label symbol at idx.
    *)
external get_label_symbol : context -> literals -> int -> symbol
	= "camlidl_z3_Z3_get_label_symbol"

(**
       Summary: Retrieve literal expression at idx.
    *)
external get_literal : context -> literals -> int -> ast
	= "camlidl_z3_Z3_get_literal"

(**
       Summary: Disable label.
       
       The disabled label is not going to be used when blocking the subsequent search.

       - {b See also}: {!Z3.block_literals}
    *)
external disable_literal : context -> literals -> int -> unit
	= "camlidl_z3_Z3_disable_literal"

(**
       Summary: Block subsequent checks using the remaining enabled labels.
    *)
external block_literals : context -> literals -> unit
	= "camlidl_z3_Z3_block_literals"

(**
       {2 {L Model navigation}}
     *)
(**
       Summary: Return the number of constants assigned by the given model.
       
        - {b Remarks}: Consider using {!Z3.get_model_constants}. 

       - {b See also}: {!Z3.get_model_constant}
    *)
external get_model_num_constants : context -> model -> int
	= "camlidl_z3_Z3_get_model_num_constants"

(**
       Summary: \[ [ get_model_constant c m i ] \]
       Return the i-th constant in the given model. 

        - {b Remarks}: Consider using {!Z3.get_model_constants}. 

       - {b Precondition}: i < get_model_num_constants c m

       - {b See also}: {!Z3.eval}
    *)
external get_model_constant : context -> model -> int -> func_decl
	= "camlidl_z3_Z3_get_model_constant"

(**
       Summary: Return the value of the given constant or function 
              in the given model.
       
    *)
external eval_func_decl : context -> model -> func_decl -> bool * ast
	= "camlidl_z3_Z3_eval_func_decl"

(**
       Summary: \[ [ is_array_value c v ] \]
       Determine whether the term encodes an array value.       
       Return the number of entries mapping to non-default values of the array.
    *)
external is_array_value : context -> model -> ast -> bool * int
	= "camlidl_z3_Z3_is_array_value"

(**
       Summary: \[ [ get_array_value c v ] \]
       An array values is represented as a dictionary plus a
       default (else) value. This function returns the array graph.

       - {b Precondition}: TRUE == is_array_value c v &num_entries       
    *)
external get_array_value : context -> model -> ast -> ast array -> ast array -> ast array * ast array * ast
	= "camlidl_z3_Z3_get_array_value"

(**
       Summary: Return the number of function interpretations in the given model.
       
       A function interpretation is represented as a finite map and an 'else' value.
       Each entry in the finite map represents the value of a function given a set of arguments.

        - {b Remarks}: Consider using {!Z3.get_model_funcs}. 
       
       - {b See also}: {!Z3.get_model_func_decl}
       - {b See also}: {!Z3.get_model_func_else}
       - {b See also}: {!Z3.get_model_func_num_entries}
       - {b See also}: {!Z3.get_model_func_entry_num_args}
       - {b See also}: {!Z3.get_model_func_entry_arg}
     *)
external get_model_num_funcs : context -> model -> int
	= "camlidl_z3_Z3_get_model_num_funcs"

(**
       Summary: \[ [ get_model_func_decl c m i ] \]
       Return the declaration of the i-th function in the given model.

        - {b Remarks}: Consider using {!Z3.get_model_funcs}. 

       - {b Precondition}: i < get_model_num_funcs c m

       - {b See also}: {!Z3.get_model_num_funcs}
    *)
external get_model_func_decl : context -> model -> int -> func_decl
	= "camlidl_z3_Z3_get_model_func_decl"

(**
       Summary: \[ [ get_model_func_else c m i ] \]
       Return the 'else' value of the i-th function interpretation in the given model.
 
       A function interpretation is represented as a finite map and an 'else' value.

        - {b Remarks}: Consider using {!Z3.get_model_funcs}. 
       
       - {b Precondition}: i < get_model_num_funcs c m

       - {b See also}: {!Z3.get_model_num_funcs}
       - {b See also}: {!Z3.get_model_func_num_entries}
       - {b See also}: {!Z3.get_model_func_entry_num_args}
       - {b See also}: {!Z3.get_model_func_entry_arg}
    *)
external get_model_func_else : context -> model -> int -> ast
	= "camlidl_z3_Z3_get_model_func_else"

(**
       Summary: \[ [ get_model_func_num_entries c m i ] \]
       Return the number of entries of the i-th function interpretation in the given model.
 
       A function interpretation is represented as a finite map and an 'else' value.

        - {b Remarks}: Consider using {!Z3.get_model_funcs}. 
       
       - {b Precondition}: i < get_model_num_funcs c m

       - {b See also}: {!Z3.get_model_num_funcs}
       - {b See also}: {!Z3.get_model_func_else}
       - {b See also}: {!Z3.get_model_func_entry_num_args}
       - {b See also}: {!Z3.get_model_func_entry_arg}
    *)
external get_model_func_num_entries : context -> model -> int -> int
	= "camlidl_z3_Z3_get_model_func_num_entries"

(**
       Summary: \[ [ get_model_func_entry_num_args c m i j ] \]
       Return the number of arguments of the j-th entry of the i-th function interpretation in the given
       model.

       A function interpretation is represented as a finite map and an 'else' value.
       This function returns the j-th entry of this map.
      
       An entry represents the value of a function given a set of arguments.
       

        - {b Remarks}: Consider using {!Z3.get_model_funcs}. 

       - {b Precondition}: i < get_model_num_funcs c m
       - {b Precondition}: j < get_model_func_num_entries c m i

       - {b See also}: {!Z3.get_model_num_funcs}
       - {b See also}: {!Z3.get_model_func_num_entries }
       - {b See also}: {!Z3.get_model_func_entry_arg}
    *)
external get_model_func_entry_num_args : context -> model -> int -> int -> int
	= "camlidl_z3_Z3_get_model_func_entry_num_args"

(**
       Summary: \[ [ get_model_func_entry_arg c m i j k ] \]
       Return the k-th argument of the j-th entry of the i-th function interpretation in the given
       model.

       A function interpretation is represented as a finite map and an 'else' value.
       This function returns the j-th entry of this map.
      
       An entry represents the value of a function given a set of arguments.
       

        - {b Remarks}: Consider using {!Z3.get_model_funcs}. 

       - {b Precondition}: i < get_model_num_funcs c m
       - {b Precondition}: j < get_model_func_num_entries c m i
       - {b Precondition}: k < get_model_func_entry_num_args c m i j

       - {b See also}: {!Z3.get_model_num_funcs}
       - {b See also}: {!Z3.get_model_func_num_entries }
       - {b See also}: {!Z3.get_model_func_entry_num_args}
    *)
external get_model_func_entry_arg : context -> model -> int -> int -> int -> ast
	= "camlidl_z3_Z3_get_model_func_entry_arg"

(**
       Summary: \[ [ get_model_func_entry_value c m i j ] \]
       Return the return value of the j-th entry of the i-th function interpretation in the given
       model.

       A function interpretation is represented as a finite map and an 'else' value.
       This function returns the j-th entry of this map.
      
       An entry represents the value of a function given a set of arguments.
       

        - {b Remarks}: Consider using {!Z3.get_model_funcs}. 

       - {b Precondition}: i < get_model_num_funcs c m
       - {b Precondition}: j < get_model_func_num_entries c m i

       - {b See also}: {!Z3.get_model_num_funcs}
       - {b See also}: {!Z3.get_model_func_num_entries }
    *)
external get_model_func_entry_value : context -> model -> int -> int -> ast
	= "camlidl_z3_Z3_get_model_func_entry_value"

(**
       Summary: \[ [ eval c m t ] \]
       Evaluate the AST node t in the given model. 
       
        Return a pair: Boolean and value. The Boolean is true if the term was successfully evaluated. 

       The evaluation may fail for the following reasons:

       - t contains a quantifier.

       - the model m is partial, that is, it doesn't have a complete interpretation for uninterpreted functions. 
         That is, the option {e MODEL_PARTIAL=true } was used.

       - t is type incorrect.
    *)
external eval : context -> model -> ast -> bool * ast
	= "camlidl_z3_Z3_eval"

(**
       Summary: Evaluate declaration given values.

       Provides direct way to evaluate declarations
       without going over terms.
     *)
external eval_decl : context -> model -> func_decl -> ast array -> bool * ast
	= "camlidl_z3_Z3_eval_decl"

(**
       {2 {L Interaction logging.}}
    *)
(**
       Summary: Log interaction to a file.
    *)
external open_log : context -> string -> bool
	= "camlidl_z3_Z3_open_log"

(**
       Summary: Append user-defined string to interaction log.
       
       The interaction log is opened using open_log.
       It contains the formulas that are checked using Z3.
       You can use this command to append comments, for instance.
    *)
external append_log : context -> string -> unit
	= "camlidl_z3_Z3_append_log"

(**
       Summary: Close interaction log.
    *)
external close_log : context -> unit
	= "camlidl_z3_Z3_close_log"

(**
       {2 {L String conversion}}
    *)
(**
       Summary: Select mode for the format used for pretty-printing AST nodes.

       The default mode for pretty printing AST nodes is to produce
       SMT-LIB style output where common subexpressions are printed 
       at each occurrence. The mode is called PRINT_SMTLIB_FULL.
       To print shared common subexpressions only once, 
       use the PRINT_LOW_LEVEL mode.
       To print in way that conforms to SMT-LIB standards and uses let
       expressions to share common sub-expressions use PRINT_SMTLIB_COMPLIANT.

       - {b See also}: {!Z3.ast_to_string}
       - {b See also}: {!Z3.pattern_to_string}
       - {b See also}: {!Z3.func_decl_to_string}

    *)
external set_ast_print_mode : context -> ast_print_mode -> unit
	= "camlidl_z3_Z3_set_ast_print_mode"

(**
       Summary: Convert the given AST node into a string.

       
       
       
       - {b See also}: {!Z3.pattern_to_string}
       - {b See also}: {!Z3.sort_to_string}
    *)
external ast_to_string : context -> ast -> string
	= "camlidl_z3_Z3_ast_to_string"

external pattern_to_string : context -> pattern -> string
	= "camlidl_z3_Z3_pattern_to_string"

external sort_to_string : context -> sort -> string
	= "camlidl_z3_Z3_sort_to_string"

external func_decl_to_string : context -> func_decl -> string
	= "camlidl_z3_Z3_func_decl_to_string"

(**
       Summary: Convert the given model into a string.

       
       
       
    *)
external model_to_string : context -> model -> string
	= "camlidl_z3_Z3_model_to_string"

(**
       Summary: Convert the given benchmark into SMT-LIB formatted string.

       
       
       

       
       
       
       
       
       
       
       
    *)
external benchmark_to_smtlib_string : context -> string -> string -> string -> string -> ast array -> ast -> string
	= "camlidl_z3_Z3_benchmark_to_smtlib_string_bytecode" "camlidl_z3_Z3_benchmark_to_smtlib_string"

(**
       Summary: Convert the given logical context into a string.
       
       This function is mainly used for debugging purposes. It displays
       the internal structure of a logical context.

       
       
       
    *)
external context_to_string : context -> string
	= "camlidl_z3_Z3_context_to_string"

(**
       Summary: Return runtime statistics as a string.
       
       This function is mainly used for debugging purposes. It displays
       statistics of the search activity.

       
       
       
    *)
external statistics_to_string : context -> string
	= "camlidl_z3_Z3_statistics_to_string"

(**
       Summary: Extract satisfying assignment from context as a conjunction.
       
       This function can be used for debugging purposes. It returns a conjunction
       of formulas that are assigned to true in the current context.
       This conjunction will contain not only the assertions that are set to true
       under the current assignment, but will also include additional literals
       if there has been a call to {!Z3.check} or {!Z3.check_and_get_model}.       
     *)
external get_context_assignment : context -> ast
	= "camlidl_z3_Z3_get_context_assignment"

(**
       {2 {L Parser interface}}
    *)
(**
       Summary: \[ [ parse_smtlib_string c str sort_names sorts decl_names decls ] \]
       Parse the given string using the SMT-LIB parser. 
              
       The symbol table of the parser can be initialized using the given sorts and declarations. 
       The symbols in the arrays sort_names and decl_names don't need to match the names
       of the sorts and declarations in the arrays sorts and decls. This is an useful feature
       since we can use arbitrary names to reference sorts and declarations defined using the C API.

       The formulas, assumptions and declarations defined in str can be extracted using the functions:
       {!Z3.get_smtlib_num_formulas}, {!Z3.get_smtlib_formula}, {!Z3.get_smtlib_num_assumptions}, {!Z3.get_smtlib_assumption}, 
       {!Z3.get_smtlib_num_decls}, and {!Z3.get_smtlib_decl}.
     *)
external parse_smtlib_string : context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> unit
	= "camlidl_z3_Z3_parse_smtlib_string_bytecode" "camlidl_z3_Z3_parse_smtlib_string"

(**
       Summary: Similar to {!Z3.parse_smtlib_string}, but reads the benchmark from a file.
    *)
external parse_smtlib_file : context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> unit
	= "camlidl_z3_Z3_parse_smtlib_file_bytecode" "camlidl_z3_Z3_parse_smtlib_file"

(**
       Summary: Return the number of SMTLIB formulas parsed by the last call to {!Z3.parse_smtlib_string} or {!Z3.parse_smtlib_file}.
    *)
external get_smtlib_num_formulas : context -> int
	= "camlidl_z3_Z3_get_smtlib_num_formulas"

(**
       Summary: \[ [ get_smtlib_formula c i ] \]
       Return the i-th formula parsed by the last call to {!Z3.parse_smtlib_string} or {!Z3.parse_smtlib_file}.

       - {b Precondition}: i < get_smtlib_num_formulas c
    *)
external get_smtlib_formula : context -> int -> ast
	= "camlidl_z3_Z3_get_smtlib_formula"

(**
       Summary: Return the number of SMTLIB assumptions parsed by {!Z3.parse_smtlib_string} or {!Z3.parse_smtlib_file}.
    *)
external get_smtlib_num_assumptions : context -> int
	= "camlidl_z3_Z3_get_smtlib_num_assumptions"

(**
       Summary: \[ [ get_smtlib_assumption c i ] \]
       Return the i-th assumption parsed by the last call to {!Z3.parse_smtlib_string} or {!Z3.parse_smtlib_file}.

       - {b Precondition}: i < get_smtlib_num_assumptions c
    *)
external get_smtlib_assumption : context -> int -> ast
	= "camlidl_z3_Z3_get_smtlib_assumption"

(**
       Summary: Return the number of declarations parsed by {!Z3.parse_smtlib_string} or {!Z3.parse_smtlib_file}.
    *)
external get_smtlib_num_decls : context -> int
	= "camlidl_z3_Z3_get_smtlib_num_decls"

(**
       Summary: \[ [ get_smtlib_decl c i ] \]
       Return the i-th declaration parsed by the last call to {!Z3.parse_smtlib_string} or {!Z3.parse_smtlib_file}.

       - {b Precondition}: i < get_smtlib_num_decls c
    *)
external get_smtlib_decl : context -> int -> func_decl
	= "camlidl_z3_Z3_get_smtlib_decl"

(**
       Summary: Return the number of sorts parsed by {!Z3.parse_smtlib_string} or {!Z3.parse_smtlib_file}.
    *)
external get_smtlib_num_sorts : context -> int
	= "camlidl_z3_Z3_get_smtlib_num_sorts"

(**
       Summary: \[ [ get_smtlib_sort c i ] \]
       Return the i-th sort parsed by the last call to {!Z3.parse_smtlib_string} or {!Z3.parse_smtlib_file}.

       - {b Precondition}: i < get_smtlib_num_sorts c
    *)
external get_smtlib_sort : context -> int -> sort
	= "camlidl_z3_Z3_get_smtlib_sort"

(**
       Summary: \[ [ get_smtlib_error c ] \]
       Retrieve that last error message information generated from parsing.
    *)
external get_smtlib_error : context -> string
	= "camlidl_z3_Z3_get_smtlib_error"

(**
       Summary: \[ [ parse_z3_string c str ] \]
       Parse the given string using the Z3 native parser.
       
       Return the conjunction of asserts made in the input.
     *)
external parse_z3_string : context -> string -> ast
	= "camlidl_z3_Z3_parse_z3_string"

(**
       Summary: Similar to {!Z3.parse_z3_string}, but reads the benchmark from a file.
    *)
external parse_z3_file : context -> string -> ast
	= "camlidl_z3_Z3_parse_z3_file"

(**
       Summary: \[ [ parse_smtlib2_string c str ] \]
       Parse the given string using the SMT-LIB2 parser. 
              
       It returns a formula comprising of the conjunction of assertions in the scope
       (up to push/pop) at the end of the string.
     *)
external parse_smtlib2_string : context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> ast
	= "camlidl_z3_Z3_parse_smtlib2_string_bytecode" "camlidl_z3_Z3_parse_smtlib2_string"

(**
       Summary: Similar to {!Z3.parse_smtlib2_string}, but reads the benchmark from a file.
    *)
external parse_smtlib2_file : context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> ast
	= "camlidl_z3_Z3_parse_smtlib2_file_bytecode" "camlidl_z3_Z3_parse_smtlib2_file"

(**
       {2 {L Miscellaneous}}
    *)
(**
       Summary: Return Z3 version number information.
    *)
external get_version : unit -> int * int * int * int
	= "camlidl_z3_Z3_get_version"

(**
       Summary: Reset all allocated resources. 

       Use this facility on out-of memory errors. 
       It allows discharging the previous state and resuming afresh.
       Any pointers previously returned by the API
       become invalid.
    *)
external reset_memory : unit -> unit
	= "camlidl_z3_Z3_reset_memory"

(** 
        {2 {L External Theory Plugins}}
    *)
(**
       Summary: Create an interpreted theory sort.
    *)
external theory_mk_sort : context -> theory -> symbol -> sort
	= "camlidl_z3_Z3_theory_mk_sort"

(**
       Summary: Create an interpreted theory constant value. Values are assumed to be different from each other.
    *)
external theory_mk_value : context -> theory -> symbol -> sort -> ast
	= "camlidl_z3_Z3_theory_mk_value"

(**
       Summary: Create an interpreted constant for the given theory.
    *)
external theory_mk_constant : context -> theory -> symbol -> sort -> ast
	= "camlidl_z3_Z3_theory_mk_constant"

(**
       Summary: Create an interpreted function declaration for the given theory.
    *)
external theory_mk_func_decl : context -> theory -> symbol -> sort array -> sort -> func_decl
	= "camlidl_z3_Z3_theory_mk_func_decl"

(**
       Summary: Return the context where the given theory is installed.
    *)
external theory_get_context : theory -> context
	= "camlidl_z3_Z3_theory_get_context"

(**
       Summary: Assert a theory axiom/lemmas during the search.
       
       An axiom added at search level n will remain in the logical context until 
       level n is backtracked. 

       The callbacks for push ({!Z3.set_push_callback}) and pop
       ({!Z3.set_pop_callback}) can be used to track when the search
       level is increased (i.e., new case-split) and decreased (i.e.,
       case-split is backtracked).
       
       Z3 tracks the theory axioms asserted. So, multiple assertions of the same axiom are
       ignored.
    *)
external theory_assert_axiom : theory -> ast -> unit
	= "camlidl_z3_Z3_theory_assert_axiom"

(**
       Summary: Inform to the logical context that lhs and rhs have the same interpretation
       in the model being built by theory t. If lhs = rhs is inconsistent with other theories,
       then the logical context will backtrack.

       For more information, see the paper "Model-Based Theory Combination" in the Z3 website.
    *)
external theory_assume_eq : theory -> ast -> ast -> unit
	= "camlidl_z3_Z3_theory_assume_eq"

(**
       Summary: Enable/disable the simplification of theory axioms asserted using {!Z3.theory_assert_axiom}.
       By default, the simplification of theory specific operators is disabled. 
       That is, the reduce theory callbacks are not invoked for theory axioms.
       The default behavior is useful when asserting axioms stating properties of theory operators.
    *)
external theory_enable_axiom_simplification : theory -> bool -> unit
	= "camlidl_z3_Z3_theory_enable_axiom_simplification"

(**
       Summary: Return the root of the equivalence class containing n.
    *)
external theory_get_eqc_root : theory -> ast -> ast
	= "camlidl_z3_Z3_theory_get_eqc_root"

(**
       Summary: Return the next element in the equivalence class containing n.

       The elements in an equivalence class are organized in a circular list.
       You can traverse the list by calling this function multiple times 
       using the result from the previous call. This is illustrated in the
       code snippet below.
       {v 
           ast curr = n;
           do
             curr = theory_get_eqc_next(theory, curr);
           while (curr != n);
        v}
    *)
external theory_get_eqc_next : theory -> ast -> ast
	= "camlidl_z3_Z3_theory_get_eqc_next"

(**
       Summary: Return the number of parents of n that are operators of the given theory. 
    *)
external theory_get_num_parents : theory -> ast -> int
	= "camlidl_z3_Z3_theory_get_num_parents"

(**
       Summary: Return the i-th parent of n. 
       See {!Z3.theory_get_num_parents}. 
    *)
external theory_get_parent : theory -> ast -> int -> ast
	= "camlidl_z3_Z3_theory_get_parent"

(**
       Summary: Return TRUE if n is an interpreted theory value.
    *)
external theory_is_value : theory -> ast -> bool
	= "camlidl_z3_Z3_theory_is_value"

(**
       Summary: Return TRUE if d is an interpreted theory declaration.
    *)
external theory_is_decl : theory -> func_decl -> bool
	= "camlidl_z3_Z3_theory_is_decl"

(**
       Summary: Return the number of expressions of the given theory in
       the logical context. These are the expressions notified using the
       callback {!Z3.set_new_elem_callback}.
    *)
external theory_get_num_elems : theory -> int
	= "camlidl_z3_Z3_theory_get_num_elems"

(**
       Summary: Return the i-th elem of the given theory in the logical context.
       
       \see theory_get_num_elems
    *)
external theory_get_elem : theory -> int -> ast
	= "camlidl_z3_Z3_theory_get_elem"

(**
       Summary: Return the number of theory applications in the logical
       context. These are the expressions notified using the callback
       {!Z3.set_new_app_callback}.
    *)
external theory_get_num_apps : theory -> int
	= "camlidl_z3_Z3_theory_get_num_apps"

(**
       Summary: Return the i-th application of the given theory in the logical context.
       
       \see theory_get_num_apps
    *)
external theory_get_app : theory -> int -> ast
	= "camlidl_z3_Z3_theory_get_app"

(** 
        {2 {L Fixedpoint and Datalog facilities}}
    *)
(** 
       Summary: Add a universal Horn clause as a named rule.
       The horn_rule should be of the form:
 
       {v 
           horn_rule ::= (forall (bound-vars) horn_rule)
                      |  (=> atoms horn_rule)
                      |  atom
        v}
    *)
external datalog_add_rule : context -> ast -> symbol -> unit
	= "camlidl_z3_Z3_datalog_add_rule"

(** 
        Summary: Pose a query against the asserted rules.

        The query returns a formula that encodes the set of
        satisfying instances for the query.

        {v 
           query ::= (exists (bound-vars) query)
                 |  literals 
         v}

    *)
external datalog_query : context -> ast -> ast
	= "camlidl_z3_Z3_datalog_query"

(**
       Summary: Configure the predicate representation.

       It sets the predicate to use a set of domains given by the list of symbols.
       The domains given by the list of symbols must belong to a set
       of built-in domains.
    *)
external datalog_set_predicate_representation : context -> func_decl -> symbol array -> unit
	= "camlidl_z3_Z3_datalog_set_predicate_representation"

(**
         Summary: Parse a file in Datalog format and process the queries in it.
    *)
external datalog_parse_file : context -> string -> unit
	= "camlidl_z3_Z3_datalog_parse_file"

(**
         Summary: The following utilities allows adding user-defined domains.
    *)


(** {2 {L ML Extensions}} *)

(**
  \[ [ mk_context_x configs] \] is a shorthand for the context with configurations in [configs].
*)
val mk_context_x: (string * string) array -> context;;

(**
  \[ [ get_app_args c a ] \] is the array of arguments of an application. If [t] is a constant, then the array is empty.

  - {b See also}: {!Z3.get_app_num_args}
  - {b See also}: {!Z3.get_app_arg}
*)
val get_app_args:  context -> app -> ast array

(**
  \[ [ get_app_args c d ] \] is the array of parameters of [d].

  - {b See also}: {!Z3.get_domain_size}
  - {b See also}: {!Z3.get_domain}
*)
val get_domains: context -> func_decl -> sort array

(**
  \[ [ get_array_sort c t ] \] is the domain and the range of [t].

  - {b See also}: {!Z3.get_array_sort_domain}
  - {b See also}: {!Z3.get_array_sort_range}
*)
val get_array_sort: context -> sort -> sort * sort

(**
  \[ [ get_tuple_sort c ty ] \] is the pair [(mk_decl, fields)] where [mk_decl] is the constructor declaration of [ty], and [fields] is the array of fields in [ty].

  - {b See also}: {!Z3.get_tuple_sort_mk_decl}
  - {b See also}: {!Z3.get_tuple_sort_num_fields}
  - {b See also}: {!Z3.get_tuple_sort_field_decl}
*)
val get_tuple_sort: context -> sort -> (func_decl * func_decl array)

(**
  \[ [ datatype_constructor_refined ] \] is the refinement of a datatype constructor.
  
  It contains the constructor declaration, recognizer, and list of accessor functions.
*)
type datatype_constructor_refined = { 
   constructor : func_decl; 
   recognizer : func_decl; 
   accessors : func_decl array 
}

(**
  \[ [ get_datatype_sort c ty ] \] is the array of triples [(constructor, recognizer, fields)] where [constructor] is the constructor declaration of [ty], [recognizer] is the recognizer for the [constructor], and [fields] is the array of fields in [ty].

  - {b See also}: {!Z3.get_datatype_sort_num_constructors}
  - {b See also}: {!Z3.get_datatype_sort_constructor}
  - {b See also}: {!Z3.get_datatype_sort_recognizer}
  - {b See also}: {!Z3.get_datatype_sort_constructor_accessor}
*)


val get_datatype_sort: context -> sort -> datatype_constructor_refined array

(**
  \[ [ get_model_constants c m ] \] is the array of constants in the model [m].

  - {b See also}: {!Z3.get_model_num_constants}
  - {b See also}: {!Z3.get_model_constant}
*)
val get_model_constants: context -> model -> func_decl array


(**
  \[ [ get_model_func_entry c m i j ] \] is the [j]'th entry in the [i]'th function in the model [m].

  - {b See also}: {!Z3.get_model_func_entry_num_args}
  - {b See also}: {!Z3.get_model_func_entry_arg}
  - {b See also}: {!Z3.get_model_func_entry_value}
*)
val get_model_func_entry: context -> model -> int -> int -> (ast array * ast);;

(**
  \[ [ get_model_func_entries c m i ] \] is the array of entries in the [i]'th function in the model [m].

  - {b See also}: {!Z3.get_model_func_num_entries}
  - {b See also}: {!Z3.get_model_func_entry}
*)
val get_model_func_entries: context -> model -> int -> (ast array * ast) array;;

(**
  \[ [ get_model_funcs c m ] \] is the array of functions in the model [m]. Each function is represented by the triple [(decl, entries, else)], where [decl] is the declaration name for the function, [entries] is the array of entries in the function, and [else] is the default (else) value for the function.

  - {b See also}: {!Z3.get_model_num_funcs}
  - {b See also}: {!Z3.get_model_func_decl}
  - {b See also}: {!Z3.get_model_func_entries}
  - {b See also}: {!Z3.get_model_func_else}
*)
val get_model_funcs: context -> model -> 
  (symbol *
   (ast array * ast) array * 
   ast) array

(**
  \[ [ get_smtlib_formulas c ] \] is the array of formulas created by a preceding call to {!Z3.parse_smtlib_string} or {!Z3.parse_smtlib_file}.

  Recommend use {!Z3.parse_smtlib_string_x} or {!Z3.parse_smtlib_file_x} for functional style interface to the SMT-LIB parser.

  - {b See also}: {!Z3.parse_smtlib_string_x}
  - {b See also}: {!Z3.parse_smtlib_file_x}
  - {b See also}: {!Z3.parse_smtlib_string}
  - {b See also}: {!Z3.parse_smtlib_file}
  - {b See also}: {!Z3.get_smtlib_num_formulas}
  - {b See also}: {!Z3.get_smtlib_formula}
*)
val get_smtlib_formulas: context -> ast array

(**
  \[ [get_smtlib_assumptions c] \] is the array of assumptions created by a preceding call to {!Z3.parse_smtlib_string} or {!Z3.parse_smtlib_file}.

  Recommend use {!Z3.parse_smtlib_string_x} or {!Z3.parse_smtlib_file_x} for functional style interface to the SMT-LIB parser.


  - {b See also}: {!Z3.parse_smtlib_string_x}
  - {b See also}: {!Z3.parse_smtlib_file_x}
  - {b See also}: {!Z3.parse_smtlib_string}
  - {b See also}: {!Z3.parse_smtlib_file}
  - {b See also}: {!Z3.get_smtlib_num_assumptions}
  - {b See also}: {!Z3.get_smtlib_assumption}
*)
val get_smtlib_assumptions: context -> ast array

(**
  \[ [ get_smtlib_decls c ] \] is the array of declarations created by a preceding call to {!Z3.parse_smtlib_string} or {!Z3.parse_smtlib_file}.

  Recommend use {!Z3.parse_smtlib_string_x} or {!Z3.parse_smtlib_file_x} for functional style interface to the SMT-LIB parser.


  - {b See also}: {!Z3.parse_smtlib_string_x}
  - {b See also}: {!Z3.parse_smtlib_file_x}
  - {b See also}: {!Z3.parse_smtlib_string}
  - {b See also}: {!Z3.parse_smtlib_file}
  - {b See also}: {!Z3.get_smtlib_num_decls}
  - {b See also}: {!Z3.get_smtlib_decl}
*)
val get_smtlib_decls: context -> func_decl array

(**
  \[ [ get_smtlib_parse_results c ] \] is the triple [(get_smtlib_formulas c, get_smtlib_assumptions c, get_smtlib_decls c)].

  Recommend use {!Z3.parse_smtlib_string_x} or {!Z3.parse_smtlib_file_x} for functional style interface to the SMT-LIB parser.


  - {b See also}: {!Z3.parse_smtlib_string_x}
  - {b See also}: {!Z3.parse_smtlib_file_x}
  - {b See also}: {!Z3.parse_smtlib_string}
  - {b See also}: {!Z3.parse_smtlib_file}
  - {b See also}: {!Z3.get_smtlib_formulas}
  - {b See also}: {!Z3.get_smtlib_assumptions}
  - {b See also}: {!Z3.get_smtlib_decls}
*)
val get_smtlib_parse_results: context -> (ast array * ast array * func_decl array)

(**
  \[ [ parse_smtlib_string_formula c ... ] \] calls [(parse_smtlib_string c ...)] and returns the single formula produced. 

  Recommended for functional style interface to the SMT-LIB parser.

  - {b See also}: {!Z3.parse_smtlib_file_formula}
  - {b See also}: {!Z3.parse_smtlib_string_x}
*)
val parse_smtlib_string_formula: context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> ast

(**
  \[ [ parse_smtlib_file_formula c ... ] \] calls [(parse_smtlib_file c ...)] and returns the single formula produced. 

  Recommended for functional style interface to the SMT-LIB parser.

  - {b See also}: {!Z3.parse_smtlib_file_formula}
  - {b See also}: {!Z3.parse_smtlib_file_x}
*)
val parse_smtlib_file_formula: context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> ast

(**
  \[ [ parse_smtlib_string_x c ... ] \] is [(parse_smtlib_string c ...; get_smtlib_parse_results c)]

  Recommended for functional style interface to the SMT-LIB parser.

  - {b See also}: {!Z3.parse_smtlib_file_x}
  - {b See also}: {!Z3.parse_smtlib_string}
  - {b See also}: {!Z3.get_smtlib_parse_results}
*)
val parse_smtlib_string_x: context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> (ast array * ast array * func_decl array)

(**
  \[ [ parse_smtlib_file_x c ... ] \] is [(parse_smtlib_file c ...; get_smtlib_parse_results c)]

  Recommended for functional style interface to the SMT-LIB parser.

  - {b See also}: {!Z3.parse_smtlib_string_x}
  - {b See also}: {!Z3.parse_smtlib_file}
  - {b See also}: {!Z3.get_smtlib_parse_results}
*)
val parse_smtlib_file_x: context -> string -> symbol array -> sort array -> symbol array -> func_decl array -> (ast array * ast array * func_decl array)

(**
  \[ [ symbol_refined ] \] is the refinement of a {!Z3.symbol} .

  - {b See also}: {!Z3.symbol_refine}
  - {b See also}: {!Z3.get_symbol_kind}
*)
type symbol_refined =
  | Symbol_int of int
  | Symbol_string of string
  | Symbol_unknown;;

(**
  \[ [ symbol_refine c s ] \] is the refined symbol of [s].

  - {b See also}:  {!Z3.symbol_refined}
  - {b See also}: {!Z3.get_symbol_kind}
*)
val symbol_refine: context -> symbol -> symbol_refined;;

(**
  \[ [ sort_refined ] \] is the refinement of a {!Z3.sort} .

  - {b See also}: {!Z3.sort_refine}
  - {b See also}: {!Z3.get_sort_kind}
*)


type sort_refined =
  | Sort_uninterpreted of symbol
  | Sort_bool
  | Sort_int
  | Sort_real
  | Sort_bv of int
  | Sort_array of (sort * sort)
  | Sort_datatype of datatype_constructor_refined array
  | Sort_relation
  | Sort_finite_domain
  | Sort_unknown of symbol

(**
  \[ [ sort_refine c t ] \] is the refined sort of [t].

  - {b See also}:  {!Z3.sort_refined}
  - {b See also}: {!Z3.get_sort_kind}
*)
val sort_refine: context -> sort -> sort_refined;;

(**
  \[ [ binder_type ] \] is a universal or existential quantifier.

  - {b See also}: {!Z3.term_refined}
*)
type binder_type = | Forall | Exists 

(**
  \[ [ numeral_refined ] \] is the refinement of a numeral .

  Numerals whose fractional representation can be fit with
  64 bit integers are treated as small.

*)
type numeral_refined = 
  | Numeral_small  of int64 * int64
  | Numeral_large  of string

(**
  \[ [ term_refined ] \] is the refinement of a {!Z3.ast} .

  - {b See also}: {!Z3.term_refine}
*)
type term_refined = 
  | Term_app        of decl_kind * func_decl * ast array
  | Term_quantifier of binder_type * int * ast array array * (symbol * sort) array * ast
  | Term_numeral    of numeral_refined * sort
  | Term_var        of int * sort

(**
  \[ [ term_refine c a ] \] is the refined term of [a].

  - {b See also}:  {!Z3.term_refined}
*)
val term_refine : context -> ast -> term_refined

(** 
  \[ [mk_theory c name ] \] create a custom theory.

*)
val mk_theory : context -> string -> theory

(**
  \[ [set_delete_callback th cb] \] set callback when theory gets deleted.
*)
val set_delete_callback : theory -> (unit -> unit) -> unit

(**
  \[ [set_reduce_app_callback th cb] \] set callback for simplifying theory terms.
*)
val set_reduce_app_callback : theory -> (func_decl -> ast array -> ast option) -> unit

(**
  \[ [set_reduce_eq_callback th cb] \] set callback for simplifying equalities over theory terms.
*)
val set_reduce_eq_callback : theory -> (ast -> ast -> ast option) -> unit

(**
  \[ [set_reduce_distinct_callback th cb] \] set callback for simplifying disequalities over theory terms.
*)
val set_reduce_distinct_callback : theory -> (ast array -> ast option) -> unit

(**
  \[ [set_new_app_callback th cb] \] set callback for registering new application.
*)
val set_new_app_callback : theory -> (ast -> unit) -> unit

(**
  \[ [set_new_elem_callback th cb] \] set callback for registering new element.

  - {b See also}: the help for the corresponding C API function.  
*)
val set_new_elem_callback : theory -> (ast -> unit) -> unit

(**
  \[ [set_init_search_callback th cb] \] set callback when Z3 starts searching for a satisfying assignment.
*)
val set_init_search_callback : theory -> (unit -> unit) -> unit

(**
  \[ [set_push_callback th cb] \] set callback for a logical context push.
*)
val set_push_callback : theory -> (unit -> unit) -> unit

(**
  \[ [set_pop_callback th cb] \] set callback for a logical context pop.
*)
val set_pop_callback : theory -> (unit -> unit) -> unit

(**
  \[ [set_restart_callback th cb] \] set callback for search restart.
*)
val set_restart_callback : theory -> (unit -> unit) -> unit

val set_reset_callback : theory -> (unit -> unit) -> unit

val set_final_check_callback : theory -> (unit -> bool) -> unit

val set_new_eq_callback : theory -> (ast -> ast -> unit) -> unit

val set_new_diseq_callback : theory -> (ast -> ast -> unit) -> unit

val set_new_assignment_callback : theory -> (ast -> bool -> unit) -> unit

val set_new_relevant_callback : theory -> (ast -> unit) -> unit



