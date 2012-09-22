DEFINE_TYPE(Z3_config);
DEFINE_TYPE(Z3_context);
DEFINE_TYPE(Z3_sort);
DEFINE_TYPE(Z3_func_decl);
DEFINE_TYPE(Z3_ast);
DEFINE_TYPE(Z3_app);
DEFINE_TYPE(Z3_pattern);
DEFINE_TYPE(Z3_symbol);
DEFINE_TYPE(Z3_parameter);
DEFINE_TYPE(Z3_model);
DEFINE_TYPE(Z3_literals);
DEFINE_TYPE(Z3_constructor);
DEFINE_TYPE(Z3_constructor_list);
DEFINE_TYPE(Z3_theory);
DEFINE_VOID(Z3_theory_data);


#ifndef __int64
#define __int64 long long
#endif

#ifndef __uint64
#define __uint64 unsigned long long
#endif

// Backwards compatibility
#define Z3_type_ast            Z3_sort
#define Z3_const_decl_ast      Z3_func_decl
#define Z3_const               Z3_app
#define Z3_pattern_ast         Z3_pattern
#define Z3_UNINTERPRETED_TYPE  Z3_UNINTERPRETED_SORT
#define Z3_BOOL_TYPE           Z3_BOOL_SORT
#define Z3_INT_TYPE            Z3_INT_SORT
#define Z3_REAL_TYPE           Z3_REAL_SORT
#define Z3_BV_TYPE             Z3_BV_SORT
#define Z3_ARRAY_TYPE          Z3_ARRAY_SORT
#define Z3_TUPLE_TYPE          Z3_DATATYPE_SORT
#define Z3_UNKNOWN_TYPE        Z3_UNKNOWN_SORT
#define Z3_CONST_DECL_AST      Z3_FUNC_DECL_AST    
#define Z3_TYPE_AST            Z3_SORT_AST          
#define Z3_SORT_ERROR          Z3_TYPE_ERROR
#define Z3_mk_uninterpreted_type Z3_mk_uninterpreted_sort
#define Z3_mk_bool_type        Z3_mk_bool_sort
#define Z3_mk_int_type         Z3_mk_int_sort
#define Z3_mk_real_type        Z3_mk_real_sort
#define Z3_mk_bv_type          Z3_mk_bv_sort
#define Z3_mk_array_type       Z3_mk_array_sort
#define Z3_mk_tuple_type       Z3_mk_tuple_sort
#define Z3_get_type            Z3_get_sort
#define Z3_get_pattern_ast           Z3_get_pattern
#define Z3_get_type_kind             Z3_get_sort_kind
#define Z3_get_type_name             Z3_get_sort_name
#define Z3_get_bv_type_size          Z3_get_bv_sort_size
#define Z3_get_array_type_domain     Z3_get_array_sort_domain
#define Z3_get_array_type_range      Z3_get_array_sort_range
#define Z3_get_tuple_type_num_fields Z3_get_tuple_sort_num_fields
#define Z3_get_tuple_type_field_decl Z3_get_tuple_sort_field_decl
#define Z3_get_tuple_type_mk_decl    Z3_get_tuple_sort_mk_decl
#define Z3_to_const_ast              Z3_to_app
#define Z3_get_numeral_value_string  Z3_get_numeral_string
#define Z3_get_const_ast_decl        Z3_get_app_decl
#define Z3_get_value                 Z3_eval_func_decl

/**
   \defgroup capi C API

*/
/*@{*/

/**
   \conly @name Types
   
   \conly Most of the types in the C API are opaque pointers.

   \conly - \c Z3_config: a configuration object used to initialize logical contexts.
   \conly - \c Z3_context: logical context. This is the main Z3 data-structure.
   \conly - \c Z3_symbol: a Lisp-link symbol. It is used to name types, constants, and functions.  A symbol can be created using
   \conly string or integers. 
   \conly - \c Z3_ast: abstract syntax tree node. That is, the data-structure used in Z3 to represent terms, formulas and types.
   \conly - \c Z3_sort: a kind of AST used to represent types.
   \conly - \c Z3_app: a kind of AST used to represent constant and function declarations.
   \conly - \c Z3_pattern: a kind of AST used to represent pattern and multi-patterns used to guide quantifier instantiation.
   \conly - \c Z3_model: a model for the constraints asserted into the logical context.
*/

#ifndef CAMLIDL
/**
   \conly \brief Z3 Boolean type. It is just an alias for \c int.
*/
typedef int Z3_bool;
#else
/**
   \conly \brief Z3 Boolean type. It is just an alias for \c Boolean.
*/
#define Z3_bool boolean
#endif // CAMLIDL

#ifndef CAMLIDL
/**
   \conly \brief Z3 string type. It is just an alias for <tt>const char *</tt>.
*/
typedef const char * Z3_string;
typedef Z3_string * Z3_string_ptr;
#else
/**
   \conly \brief Z3 string type. It is just an alias for <tt>[string] const char *</tt>.
*/
#define Z3_string [string] const char *
/* hack to make the IDL compiler happy */
#define Z3_string_ptr const char * *
#endif // CAMLIDL
    
#ifndef CAMLIDL
/**
   \conly \brief True value. It is just an alias for \c 1.
*/
#define Z3_TRUE  1

/**
   \conly \brief False value. It is just an alias for \c 0.
*/
#define Z3_FALSE 0

#endif // CAMLIDL

/**
   \conly \brief Lifted Boolean type: \c false, \c undefined, \c true.
*/
typedef enum 
{
    Z3_L_FALSE = -1,
    Z3_L_UNDEF,
    Z3_L_TRUE
} Z3_lbool;

/**
   \conly \brief In Z3, a symbol can be represented using integers and strings (See #Z3_get_symbol_kind).

   \conly \sa Z3_mk_int_symbol
   \conly \sa Z3_mk_string_symbol
*/
typedef enum 
{
    Z3_INT_SYMBOL,
    Z3_STRING_SYMBOL 
} Z3_symbol_kind;


/**
   \conly \brief The different kinds of parameters that can be associated with function symbols.
   \conly \sa Z3_get_decl_num_parameters
   \conly \sa Z3_get_decl_parameter_kind

   \conly - Z3_PARAMETER_INT is used for integer parameters.
   \conly - Z3_PARAMETER_DOUBLE is used for double parameters.
   \conly - Z3_PARAMETER_RATIONAL is used for parameters that are rational numbers.
   \conly - Z3_PARAMETER_SORT is used for sort parameters.
   \conly - Z3_PARAMETER_AST is used for expression parameters.
   \conly - Z3_PARAMETER_FUNC_DECL is used for function declaration parameters.
*/
typedef enum 
{
    Z3_PARAMETER_INT,
    Z3_PARAMETER_DOUBLE,
    Z3_PARAMETER_RATIONAL,
    Z3_PARAMETER_SYMBOL,
    Z3_PARAMETER_SORT,
    Z3_PARAMETER_AST,
    Z3_PARAMETER_FUNC_DECL,
} Z3_parameter_kind;

/**
   \conly \brief The different kinds of Z3 types (See #Z3_get_sort_kind).
*/
typedef enum 
{
    Z3_UNINTERPRETED_SORT,
    Z3_BOOL_SORT,
    Z3_INT_SORT,
    Z3_REAL_SORT,
    Z3_BV_SORT,
    Z3_ARRAY_SORT,
    Z3_DATATYPE_SORT,
    Z3_RELATION_SORT,
    Z3_FINITE_DOMAIN_SORT,
    Z3_UNKNOWN_SORT = 1000
} Z3_sort_kind;

/**
   \conly \brief The different kinds of Z3 AST (abstract syntax trees). That is, terms, formulas and types.

   \conly - Z3_APP_AST:            constant and applications 
   \conly - Z3_NUMERAL_AST:        numeral constants
   \conly - Z3_VAR_AST:            bound variables 
   \conly - Z3_QUANTIFIER_AST:     quantifiers 
   \conly - Z3_UNKNOWN_AST:        internal 
*/
typedef enum 
{
    Z3_NUMERAL_AST,
    Z3_APP_AST,         
    Z3_VAR_AST,          
    Z3_QUANTIFIER_AST,    
    Z3_UNKNOWN_AST = 1000 
} Z3_ast_kind;

/**
   \conly \brief The different kinds of interpreted function kinds.

   (*
   - Z3_OP_TRUE The constant true.

   - Z3_OP_FALSE The constant false.

   - Z3_OP_EQ The equality predicate.

   - Z3_OP_DISTINCT The n-ary distinct predicate (every argument is mutually distinct).

   - Z3_OP_ITE The ternary if-then-else term.

   - Z3_OP_AND n-ary conjunction.

   - Z3_OP_OR n-ary disjunction.

   - Z3_OP_IFF equivalence (binary).

   - Z3_OP_XOR Exclusive or.

   - Z3_OP_NOT Negation.

   - Z3_OP_IMPLIES Implication.

   - Z3_OP_OEQ Binary equivalence modulo namings. This binary predicate is used in proof terms.
        It captures equisatisfiability and equivalence modulo renamings.

   - Z3_OP_ANUM Arithmetic numeral.

   - Z3_OP_LE <=.

   - Z3_OP_GE >=.

   - Z3_OP_LT <.

   - Z3_OP_GT >.

   - Z3_OP_ADD Addition - Binary.

   - Z3_OP_SUB Binary subtraction.

   - Z3_OP_UMINUS Unary minus.

   - Z3_OP_MUL Multiplication - Binary.

   - Z3_OP_DIV Division - Binary.

   - Z3_OP_IDIV Integer division - Binary.

   - Z3_OP_REM Remainder - Binary.

   - Z3_OP_MOD Modulus - Binary.

   - Z3_OP_TO_REAL Coercion of integer to real - Unary.

   - Z3_OP_TO_INT Coercion of real to integer - Unary.

   - Z3_OP_IS_INT Check if real is also an integer - Unary.

   - Z3_OP_STORE Array store. It satisfies select(store(a,i,v),j) = if i = j then v else select(a,j).
        Array store takes at least 3 arguments. 

   - Z3_OP_SELECT Array select. 

   - Z3_OP_CONST_ARRAY The constant array. For example, select(const(v),i) = v holds for every v and i. The function is unary.

   - Z3_OP_ARRAY_DEFAULT Default value of arrays. For example default(const(v)) = v. The function is unary.

   - Z3_OP_ARRAY_MAP Array map operator.
         It satisfies map[f](a1,..,a_n)[i] = f(a1[i],...,a_n[i]) for every i.

   - Z3_OP_SET_UNION Set union between two Booelan arrays (two arrays whose range type is Boolean). The function is binary.

   - Z3_OP_SET_INTERSECT Set intersection between two Boolean arrays. The function is binary.

   - Z3_OP_SET_DIFFERENCE Set difference between two Boolean arrays. The function is binary.

   - Z3_OP_SET_COMPLEMENT Set complement of a Boolean array. The function is unary.

   - Z3_OP_SET_SUBSET Subset predicate between two Boolean arrays. The relation is binary.

   - Z3_OP_AS_ARRAY An array value that behaves as the function graph of the
                    function passed as parameter.

   - Z3_OP_BNUM Bit-vector numeral.

   - Z3_OP_BIT1 One bit bit-vector.

   - Z3_OP_BIT0 Zero bit bit-vector.

   - Z3_OP_BNEG Unary minus.

   - Z3_OP_BADD Binary addition.

   - Z3_OP_BSUB Binary subtraction.

   - Z3_OP_BMUL Binary multiplication.
    
   - Z3_OP_BSDIV Binary signed division.

   - Z3_OP_BUDIV Binary unsigned division.

   - Z3_OP_BSREM Binary signed remainder.

   - Z3_OP_BUREM Binary unsigned remainder.

   - Z3_OP_BSMOD Binary signed modulus.

   - Z3_OP_BSDIV0 Unary function. bsdiv(x,0) is congruent to bsdiv0(x).

   - Z3_OP_BUDIV0 Unary function. budiv(x,0) is congruent to budiv0(x).

   - Z3_OP_BSREM0 Unary function. bsrem(x,0) is congruent to bsrem0(x).

   - Z3_OP_BUREM0 Unary function. burem(x,0) is congruent to burem0(x).

   - Z3_OP_BSMOD0 Unary function. bsmod(x,0) is congruent to bsmod0(x).
    
   - Z3_OP_ULEQ Unsigned bit-vector <= - Binary relation.

   - Z3_OP_SLEQ Signed bit-vector  <= - Binary relation.

   - Z3_OP_UGEQ Unsigned bit-vector  >= - Binary relation.

   - Z3_OP_SGEQ Signed bit-vector  >= - Binary relation.

   - Z3_OP_ULT Unsigned bit-vector  < - Binary relation.

   - Z3_OP_SLT Signed bit-vector < - Binary relation.

   - Z3_OP_UGT Unsigned bit-vector > - Binary relation.

   - Z3_OP_SGT Signed bit-vector > - Binary relation.

   - Z3_OP_BAND Bit-wise and - Binary.

   - Z3_OP_BOR Bit-wise or - Binary.

   - Z3_OP_BNOT Bit-wise not - Unary.

   - Z3_OP_BXOR Bit-wise xor - Binary.

   - Z3_OP_BNAND Bit-wise nand - Binary.

   - Z3_OP_BNOR Bit-wise nor - Binary.

   - Z3_OP_BXNOR Bit-wise xnor - Binary.

   - Z3_OP_CONCAT Bit-vector concatenation - Binary.

   - Z3_OP_SIGN_EXT Bit-vector sign extension.

   - Z3_OP_ZERO_EXT Bit-vector zero extension.

   - Z3_OP_EXTRACT Bit-vector extraction.

   - Z3_OP_REPEAT Repeat bit-vector n times.

   - Z3_OP_BREDOR Bit-vector reduce or - Unary.

   - Z3_OP_BREDAND Bit-vector reduce and - Unary.

   - Z3_OP_BCOMP .

   - Z3_OP_BSHL Shift left.

   - Z3_OP_BLSHR Logical shift right.

   - Z3_OP_BASHR Arithmetical shift right.

   - Z3_OP_ROTATE_LEFT Left rotation.

   - Z3_OP_ROTATE_RIGHT Right rotation.

   - Z3_OP_EXT_ROTATE_LEFT (extended) Left rotation. Similar to Z3_OP_ROTATE_LEFT, but it is a binary operator instead of a parametric one.

   - Z3_OP_EXT_ROTATE_RIGHT (extended) Right rotation. Similar to Z3_OP_ROTATE_RIGHT, but it is a binary operator instead of a parametric one.

   - Z3_OP_INT2BV Coerce integer to bit-vector. NB. This function
       is not supported by the decision procedures. Only the most
       rudimentary simplification rules are applied to this function.

   - Z3_OP_BV2INT Coerce bit-vector to integer. NB. This function
       is not supported by the decision procedures. Only the most
       rudimentary simplification rules are applied to this function.

   - Z3_OP_CARRY Compute the carry bit in a full-adder. 
       The meaning is given by the equivalence
       (carry l1 l2 l3) <=> (or (and l1 l2) (and l1 l3) (and l2 l3)))

   - Z3_OP_XOR3 Compute ternary XOR.
       The meaning is given by the equivalence
       (xor3 l1 l2 l3) <=> (xor (xor l1 l2) l3)

   - Z3_OP_PR_TRUE: Proof for the expression 'true'.

   - Z3_OP_PR_ASSERTED: Proof for a fact asserted by the user.
   
   - Z3_OP_PR_GOAL: Proof for a fact (tagged as goal) asserted by the user.

   - Z3_OP_PR_MODUS_PONENS: Given a proof for p and a proof for (implies p q), produces a proof for q.
       \nicebox{
          T1: p
          T2: (implies p q)
          [mp T1 T2]: q
          }
          The second antecedents may also be a proof for (iff p q).

   - Z3_OP_PR_REFLEXIVITY: A proof for (R t t), where R is a reflexive relation. This proof object has no antecedents.
        The only reflexive relations that are used are 
        equivalence modulo namings, equality and equivalence.
        That is, R is either '~', '=' or 'iff'.

   - Z3_OP_PR_SYMMETRY: Given an symmetric relation R and a proof for (R t s), produces a proof for (R s t).
          \nicebox{
          T1: (R t s)
          [symmetry T1]: (R s t)
          }
          T1 is the antecedent of this proof object.

   - Z3_OP_PR_TRANSITIVITY: Given a transitive relation R, and proofs for (R t s) and (R s u), produces a proof
       for (R t u).
       \nicebox{
       T1: (R t s)
       T2: (R s u)
       [trans T1 T2]: (R t u)
       }

   - Z3_OP_PR_TRANSITIVITY_STAR: Condensed transitivity proof. This proof object is only used if the parameter PROOF_MODE is 1.
     It combines several symmetry and transitivity proofs. 

          Example:
          \nicebox{
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

   - Z3_OP_PR_MONOTONICITY: Monotonicity proof object.
          \nicebox{
          T1: (R t_1 s_1)
          ...
          Tn: (R t_n s_n)
          [monotonicity T1 ... Tn]: (R (f t_1 ... t_n) (f s_1 ... s_n))
          }
          Remark: if t_i == s_i, then the antecedent Ti is suppressed.
          That is, reflexivity proofs are supressed to save space.

   - Z3_OP_PR_QUANT_INTRO: Given a proof for (~ p q), produces a proof for (~ (forall (x) p) (forall (x) q)).

       T1: (~ p q)
       [quant-intro T1]: (~ (forall (x) p) (forall (x) q))
   
   - Z3_OP_PR_DISTRIBUTIVITY: Distributivity proof object. 
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
    
   - Z3_OP_PR_AND_ELIM: Given a proof for (and l_1 ... l_n), produces a proof for l_i
        
       \nicebox{
       T1: (and l_1 ... l_n)
       [and-elim T1]: l_i
       }
   - Z3_OP_PR_NOT_OR_ELIM: Given a proof for (not (or l_1 ... l_n)), produces a proof for (not l_i).

       \nicebox{
       T1: (not (or l_1 ... l_n))
       [not-or-elim T1]: (not l_i)
       }

   - Z3_OP_PR_REWRITE: A proof for a local rewriting step (= t s).
          The head function symbol of t is interpreted.

          This proof object has no antecedents.
          The conclusion of a rewrite rule is either an equality (= t s), 
          an equivalence (iff t s), or equi-satisfiability (~ t s).
          Remark: if f is bool, then = is iff.
          

          Examples:
          \nicebox{
          (= (+ x 0) x)
          (= (+ x 1 2) (+ 3 x))
          (iff (or x false) x)
          }

   - Z3_OP_PR_REWRITE_STAR: A proof for rewriting an expression t into an expression s.
       This proof object is used if the parameter PROOF_MODE is 1.
       This proof object can have n antecedents.
       The antecedents are proofs for equalities used as substitution rules.
       The object is also used in a few cases if the parameter PROOF_MODE is 2.
       The cases are:
         - When applying contextual simplification (CONTEXT_SIMPLIFIER=true)
         - When converting bit-vectors to Booleans (BIT2BOOL=true)
         - When pulling ite expression up (PULL_CHEAP_ITE_TREES=true)

   - Z3_OP_PR_PULL_QUANT: A proof for (iff (f (forall (x) q(x)) r) (forall (x) (f (q x) r))). This proof object has no antecedents.

   - Z3_OP_PR_PULL_QUANT_STAR: A proof for (iff P Q) where Q is in prenex normal form.
       This proof object is only used if the parameter PROOF_MODE is 1.       
       This proof object has no antecedents.
  
   - Z3_OP_PR_PUSH_QUANT: A proof for:

       \nicebox{
          (iff (forall (x_1 ... x_m) (and p_1[x_1 ... x_m] ... p_n[x_1 ... x_m]))
               (and (forall (x_1 ... x_m) p_1[x_1 ... x_m])
                 ... 
               (forall (x_1 ... x_m) p_n[x_1 ... x_m])))
               }
         This proof object has no antecedents.

   - Z3_OP_PR_ELIM_UNUSED_VARS:  
          A proof for (iff (forall (x_1 ... x_n y_1 ... y_m) p[x_1 ... x_n])
                           (forall (x_1 ... x_n) p[x_1 ... x_n])) 

          It is used to justify the elimination of unused variables.
          This proof object has no antecedents.

   - Z3_OP_PR_DER: A proof for destructive equality resolution:
          (iff (forall (x) (or (not (= x t)) P[x])) P[t])
          if x does not occur in t.

          This proof object has no antecedents.
          
          Several variables can be eliminated simultaneously.

   - Z3_OP_PR_QUANT_INST: A proof of (or (not (forall (x) (P x))) (P a))

   - Z3_OP_PR_HYPOTHESIS: Mark a hypothesis in a natural deduction style proof.

   - Z3_OP_PR_LEMMA: 

       \nicebox{
          T1: false
          [lemma T1]: (or (not l_1) ... (not l_n))
          }
          This proof object has one antecedent: a hypothetical proof for false.
          It converts the proof in a proof for (or (not l_1) ... (not l_n)),
          when T1 contains the hypotheses: l_1, ..., l_n.

   - Z3_OP_PR_UNIT_RESOLUTION: 
       \nicebox{
          T1:      (or l_1 ... l_n l_1' ... l_m')
          T2:      (not l_1)
          ...
          T(n+1):  (not l_n)
          [unit-resolution T1 ... T(n+1)]: (or l_1' ... l_m')
          }

   - Z3_OP_PR_IFF_TRUE: 
      \nicebox{
       T1: p
       [iff-true T1]: (iff p true)
       }

   - Z3_OP_PR_IFF_FALSE:
      \nicebox{
       T1: (not p)
       [iff-false T1]: (iff p false)
       }

   - Z3_OP_PR_COMMUTATIVITY:

          [comm]: (= (f a b) (f b a))
          
          f is a commutative operator.

          This proof object has no antecedents.
          Remark: if f is bool, then = is iff.
   
   - Z3_OP_PR_DEF_AXIOM: Proof object used to justify Tseitin's like axioms:
       
          \nicebox{
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
    
   - Z3_OP_PR_DEF_INTRO: Introduces a name for a formula/term.
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

   - Z3_OP_PR_APPLY_DEF: 
       [apply-def T1]: F ~ n
       F is 'equivalent' to n, given that T1 is a proof that
       n is a name for F.
   
   - Z3_OP_PR_IFF_OEQ:
       T1: (iff p q)
       [iff~ T1]: (~ p q)
 
   - Z3_OP_PR_NNF_POS: Proof for a (positive) NNF step. Example:
       \nicebox{
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
        \nicebox{
           T1: q ~ q_new 
           [nnf-pos T1]: (~ (forall (x T) q) (forall (x T) q_new))
        }
       (b) When recursively creating NNF over Boolean formulas, where the top-level
       connective is changed during NNF conversion. The relevant Boolean connectives
       for NNF_POS are 'implies', 'iff', 'xor', 'ite'.
       NNF_NEG furthermore handles the case where negation is pushed
       over Boolean connectives 'and' and 'or'.

    
   - Z3_OP_PR_NFF_NEG: Proof for a (negative) NNF step. Examples:
          \nicebox{
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
   - Z3_OP_PR_NNF_STAR: A proof for (~ P Q) where Q is in negation normal form.
       
       This proof object is only used if the parameter PROOF_MODE is 1.       
              
       This proof object may have n antecedents. Each antecedent is a PR_DEF_INTRO.

   - Z3_OP_PR_CNF_STAR: A proof for (~ P Q) where Q is in conjunctive normal form.
       This proof object is only used if the parameter PROOF_MODE is 1.       
       This proof object may have n antecedents. Each antecedent is a PR_DEF_INTRO.          

   - Z3_OP_PR_SKOLEMIZE: Proof for:  
       
          \nicebox{
          [sk]: (~ (not (forall x (p x y))) (not (p (sk y) y)))
          [sk]: (~ (exists x (p x y)) (p (sk y) y))
          }

          This proof object has no antecedents.
   
   - Z3_OP_PR_MODUS_PONENS_OEQ: Modus ponens style rule for equi-satisfiability.
       \nicebox{
          T1: p
          T2: (~ p q)
          [mp~ T1 T2]: q
          }

    - Z3_OP_PR_TH_LEMMA: Generic proof for theory lemmas.

         The theory lemma function comes with one or more parameters.
         The first parameter indicates the name of the theory.
         For the theory of arithmetic, additional parameters provide hints for
         checking the theory lemma. 
         The hints for arithmetic are:
         
         - farkas - followed by rational coefficients. Multiply the coefficients to the
           inequalities in the lemma, add the (negated) inequalities and obtain a contradiction.

         - triangle-eq - Indicates a lemma related to the equivalence:
         \nicebox{
            (iff (= t1 t2) (and (<= t1 t2) (<= t2 t1)))
         }

         - gcd-test - Indicates an integer linear arithmetic lemma that uses a gcd test.


      - Z3_OP_RA_STORE: Insert a record into a relation.
        The function takes \c n+1 arguments, where the first argument is the relation and the remaining \c n elements 
        correspond to the \c n columns of the relation.

      - Z3_OP_RA_EMPTY: Creates the empty relation. 
        
      - Z3_OP_RA_IS_EMPTY: Tests if the relation is empty.

      - Z3_OP_RA_JOIN: Create the relational join.

      - Z3_OP_RA_UNION: Create the union or convex hull of two relations. 
        The function takes two arguments.

      - Z3_OP_RA_WIDEN: Widen two relations.
        The function takes two arguments.

      - Z3_OP_RA_PROJECT: Project the columns (provided as numbers in the parameters).
        The function takes one argument.

      - Z3_OP_RA_FILTER: Filter (restrict) a relation with respect to a predicate.
        The first argument is a relation. 
        The second argument is a predicate with free de-Brujin indices
        corresponding to the columns of the relation.
        So the first column in the relation has index 0.

      - Z3_OP_RA_NEGATION_FILTER: Intersect the first relation with respect to negation
        of the second relation (the function takes two arguments).
        Logically, the specification can be described by a function

           target = filter_by_negation(pos, neg, columns)

        where columns are pairs c1, d1, .., cN, dN of columns from pos and neg, such that
        target are elements in x in pos, such that there is no y in neg that agrees with
        x on the columns c1, d1, .., cN, dN.

    
      - Z3_OP_RA_RENAME: rename columns in the relation. 
        The function takes one argument.
        The parameters contain the renaming as a cycle.
         
      - Z3_OP_RA_COMPLEMENT: Complement the relation.

      - Z3_OP_RA_SELECT: Check if a record is an element of the relation.
        The function takes \c n+1 arguments, where the first argument is a relation,
        and the remaining \c n arguments correspond to a record.

      - Z3_OP_RA_CLONE: Create a fresh copy (clone) of a relation. 
        \conly The function is logically the identity, but
        \conly in the context of a register machine allows 
        \conly for #Z3_OP_RA_UNION to perform destructive updates to the first argument.
        

      - Z3_OP_FD_LT: A less than predicate over the finite domain Z3_FINITE_DOMAIN_SORT.

    *)

*/
typedef enum {
    Z3_OP_TRUE = 0x100,
    Z3_OP_FALSE,
    Z3_OP_EQ,
    Z3_OP_DISTINCT,
    Z3_OP_ITE,
    Z3_OP_AND,
    Z3_OP_OR,
    Z3_OP_IFF,
    Z3_OP_XOR,
    Z3_OP_NOT,
    Z3_OP_IMPLIES,
    Z3_OP_OEQ,


    Z3_OP_ANUM = 0x200,
    Z3_OP_LE,
    Z3_OP_GE,
    Z3_OP_LT,
    Z3_OP_GT,
    Z3_OP_ADD,
    Z3_OP_SUB,
    Z3_OP_UMINUS,
    Z3_OP_MUL,
    Z3_OP_DIV,
    Z3_OP_IDIV,
    Z3_OP_REM,
    Z3_OP_MOD,
    Z3_OP_TO_REAL,
    Z3_OP_TO_INT,
    Z3_OP_IS_INT,

    Z3_OP_STORE = 0x300,
    Z3_OP_SELECT,
    Z3_OP_CONST_ARRAY,
    Z3_OP_ARRAY_MAP,
    Z3_OP_ARRAY_DEFAULT,
    Z3_OP_SET_UNION,
    Z3_OP_SET_INTERSECT,
    Z3_OP_SET_DIFFERENCE,
    Z3_OP_SET_COMPLEMENT,
    Z3_OP_SET_SUBSET,
    Z3_OP_AS_ARRAY,

    Z3_OP_BNUM = 0x400,
    Z3_OP_BIT1,
    Z3_OP_BIT0,
    Z3_OP_BNEG,
    Z3_OP_BADD,
    Z3_OP_BSUB,
    Z3_OP_BMUL,
    
    Z3_OP_BSDIV,
    Z3_OP_BUDIV,
    Z3_OP_BSREM,
    Z3_OP_BUREM,
    Z3_OP_BSMOD,

    // special functions to record the division by 0 cases
    // these are internal functions 
    Z3_OP_BSDIV0, 
    Z3_OP_BUDIV0,
    Z3_OP_BSREM0,
    Z3_OP_BUREM0,
    Z3_OP_BSMOD0,
    
    Z3_OP_ULEQ,
    Z3_OP_SLEQ,
    Z3_OP_UGEQ,
    Z3_OP_SGEQ,
    Z3_OP_ULT,
    Z3_OP_SLT,
    Z3_OP_UGT,
    Z3_OP_SGT,

    Z3_OP_BAND,
    Z3_OP_BOR,
    Z3_OP_BNOT,
    Z3_OP_BXOR,
    Z3_OP_BNAND,
    Z3_OP_BNOR,
    Z3_OP_BXNOR,

    Z3_OP_CONCAT,
    Z3_OP_SIGN_EXT,
    Z3_OP_ZERO_EXT,
    Z3_OP_EXTRACT,
    Z3_OP_REPEAT,

    Z3_OP_BREDOR,
    Z3_OP_BREDAND,
    Z3_OP_BCOMP,

    Z3_OP_BSHL,
    Z3_OP_BLSHR,
    Z3_OP_BASHR,
    Z3_OP_ROTATE_LEFT,
    Z3_OP_ROTATE_RIGHT,
    Z3_OP_EXT_ROTATE_LEFT,
    Z3_OP_EXT_ROTATE_RIGHT,

    Z3_OP_INT2BV,
    Z3_OP_BV2INT,
    Z3_OP_CARRY,
    Z3_OP_XOR3,

    Z3_OP_PR_UNDEF = 0x500, 
    Z3_OP_PR_TRUE,
    Z3_OP_PR_ASSERTED, 
    Z3_OP_PR_GOAL, 
    Z3_OP_PR_MODUS_PONENS, 
    Z3_OP_PR_REFLEXIVITY, 
    Z3_OP_PR_SYMMETRY, 
    Z3_OP_PR_TRANSITIVITY, 
    Z3_OP_PR_TRANSITIVITY_STAR, 
    Z3_OP_PR_MONOTONICITY, 
    Z3_OP_PR_QUANT_INTRO,
    Z3_OP_PR_DISTRIBUTIVITY, 
    Z3_OP_PR_AND_ELIM, 
    Z3_OP_PR_NOT_OR_ELIM, 
    Z3_OP_PR_REWRITE, 
    Z3_OP_PR_REWRITE_STAR, 
    Z3_OP_PR_PULL_QUANT, 
    Z3_OP_PR_PULL_QUANT_STAR, 
    Z3_OP_PR_PUSH_QUANT, 
    Z3_OP_PR_ELIM_UNUSED_VARS, 
    Z3_OP_PR_DER, 
    Z3_OP_PR_QUANT_INST,
    Z3_OP_PR_HYPOTHESIS, 
    Z3_OP_PR_LEMMA, 
    Z3_OP_PR_UNIT_RESOLUTION, 
    Z3_OP_PR_IFF_TRUE, 
    Z3_OP_PR_IFF_FALSE, 
    Z3_OP_PR_COMMUTATIVITY, 
    Z3_OP_PR_DEF_AXIOM,
    Z3_OP_PR_DEF_INTRO, 
    Z3_OP_PR_APPLY_DEF, 
    Z3_OP_PR_IFF_OEQ, 
    Z3_OP_PR_NNF_POS, 
    Z3_OP_PR_NNF_NEG, 
    Z3_OP_PR_NNF_STAR, 
    Z3_OP_PR_CNF_STAR, 
    Z3_OP_PR_SKOLEMIZE,
    Z3_OP_PR_MODUS_PONENS_OEQ, 
    Z3_OP_PR_TH_LEMMA, 

    Z3_OP_RA_STORE = 0x600,
    Z3_OP_RA_EMPTY,
    Z3_OP_RA_IS_EMPTY,
    Z3_OP_RA_JOIN,
    Z3_OP_RA_UNION,
    Z3_OP_RA_WIDEN,
    Z3_OP_RA_PROJECT,
    Z3_OP_RA_FILTER,
    Z3_OP_RA_NEGATION_FILTER,
    Z3_OP_RA_RENAME,
    Z3_OP_RA_COMPLEMENT,
    Z3_OP_RA_SELECT,
    Z3_OP_RA_CLONE,
    Z3_OP_FD_LT,


    Z3_OP_UNINTERPRETED
} Z3_decl_kind;



/**
   \conly \brief The different kinds of search failure types.

   \conly - Z3_NO_FAILURE:         The last search was successful
   \conly - Z3_UNKNOWN:            Undocumented failure reason
   \conly - Z3_TIMEOUT:            Timeout
   \conly - Z3_MEMOUT_WATERMAK:    Search hit a memory high-watermak limit
   \conly - Z3_CANCELED:           External cancel flag was set
   \conly - Z3_NUM_CONFLICTS:      Maximum number of conflicts was reached
   \conly - Z3_THEORY:             Theory is incomplete
   \conly - Z3_QUANTIFIERS:        Logical context contains universal quantifiers
*/
typedef enum {
    Z3_NO_FAILURE,
    Z3_UNKNOWN,
    Z3_TIMEOUT,
    Z3_MEMOUT_WATERMARK,     
    Z3_CANCELED,      
    Z3_NUM_CONFLICTS, 
    Z3_THEORY,        
    Z3_QUANTIFIERS    
} Z3_search_failure;

/**
   \conly \brief Z3 pretty printing modes (See #Z3_set_ast_print_mode).

   \conly - Z3_PRINT_SMTLIB_FULL:   Print AST nodes in SMTLIB verbose format.
   \conly - Z3_PRINT_LOW_LEVEL:     Print AST nodes using a low-level format.
   \conly - Z3_PRINT_SMTLIB_COMPLIANT: Print AST nodes in SMTLIB 1.x compliant format.
   \conly - Z3_PRINT_SMTLIB2_COMPLIANT: Print AST nodes in SMTLIB 2.x compliant format.
*/
typedef enum {
    Z3_PRINT_SMTLIB_FULL,
    Z3_PRINT_LOW_LEVEL,
    Z3_PRINT_SMTLIB_COMPLIANT,
    Z3_PRINT_SMTLIB2_COMPLIANT
} Z3_ast_print_mode;

#ifndef CAMLIDL

/**
   \conly \brief Z3 error codes (See #Z3_get_error_code). 
   
   \conly - Z3_OK,            
   \conly - Z3_SORT_ERROR:    User tried to build an invalid (type incorrect) AST.
   \conly - Z3_IOB:           Index out of bounds 
   \conly - Z3_INVALID_ARG:   Invalid argument was provided
   \conly - Z3_PARSER_ERROR:  An error occurred when parsing a string or file.
   \conly - Z3_NO_PARSER:     Parser output is not available, that is, user didn't invoke Z3_parse_smtlib_string or Z3_parse_smtlib_file.
   \conly - Z3_INVALID_PATTERN: Invalid pattern was used to build a quantifier.
   \conly - Z3_MEMOUT_FAIL:   A memory allocation failure was encountered.
   \conly - Z3_FILE_ACCESS_ERRROR: A file could not be accessed.
   \conly - Z3_INVALID_USAGE:   API call is invalid in the current state.
   \conly - Z3_INTERNAL_FATAL: An error internal to Z3 occurred. 
   \conly - Z3_DEC_REF_ERROR: Trying decrement the reference counter of an AST that was deleted or the reference counter was not initialized with #Z3_inc_ref.
*/
typedef enum
{
    Z3_OK,            
    Z3_SORT_ERROR,    
    Z3_IOB,           
    Z3_INVALID_ARG,   
    Z3_PARSER_ERROR,  
    Z3_NO_PARSER,
    Z3_INVALID_PATTERN,
    Z3_MEMOUT_FAIL,
    Z3_FILE_ACCESS_ERROR,
    Z3_INTERNAL_FATAL,
    Z3_INVALID_USAGE,
    Z3_DEC_REF_ERROR
} Z3_error_code;



/**
   \conly \brief Z3 custom error handler (See #Z3_set_error_handler). 
*/
typedef void Z3_error_handler(Z3_error_code e);


#endif // CAMLIDL

/*@}*/

#ifndef CAMLIDL
#ifdef __cplusplus
extern "C" {
#endif // __cplusplus
#else
[pointer_default(ref)] interface Z3 {
#endif // CAMLIDL
    
    /** 
        @name Create configuration
    */
    /*@{*/

    /**
       \brief Create a configuration.

       Configurations are created in order to assign parameters prior to creating 
       contexts for Z3 interaction. For example, if the users whishes to use model
       generation, then call:

       \ccode{Z3_set_param_value(cfg\, "MODEL"\, "true")}

       \mlonly \remark Consider using {!Z3.mk_context_x} instead of using
       explicit configuration objects. The function {!Z3.mk_context_x}
       receives an array of string pairs. This array represents the
       configuration options. \endmlonly

       \sa Z3_set_param_value
       \sa Z3_del_config
    */
    Z3_config Z3_API Z3_mk_config();

    /**
       \brief Delete the given configuration object.

       \sa Z3_mk_config
    */
    void Z3_API Z3_del_config(__in Z3_config c);
    
    /**
       \brief Set a configuration parameter.

       The list of all configuration parameters can be obtained using the Z3 executable:

       \verbatim
       z3.exe -ini?
       \endverbatim

       \sa Z3_mk_config
    */
    void Z3_API Z3_set_param_value(__in Z3_config c, __in_z Z3_string param_id, __in_z Z3_string param_value);


    /*@}*/

    /**
       @name Create context
    */
    /*@{*/

    /**
       \brief Create a context using the given configuration. 
    
       After a context is created, the configuration cannot be changed.
       All main interaction with Z3 happens in the context of a \c Z3_context.

       \mlonly \remark Consider using {!Z3.mk_context_x} instead of using
       explicit configuration objects. The function {!Z3.mk_context_x}
       receives an array of string pairs. This array represents the
       configuration options. \endmlonly

       \sa Z3_del_context
    */
    Z3_context Z3_API Z3_mk_context(__in Z3_config c);

    /**
       \brief Create a context using the given configuration.
       This function is similar to #Z3_mk_context. However,
       in the context returned by this function, the user
       is responsible for managing Z3_ast reference counters.
       Managing reference counters is a burden and error-prone,
       but allows the user to use the memory more efficiently. 
       The user must invoke #Z3_inc_ref for any Z3_ast returned
       by Z3, and #Z3_dec_ref whenever the Z3_ast is not needed
       anymore. This idiom is similar to the one used in
       BDD (binary decision diagrams) packages such as CUDD.

       Remark: Z3_sort, Z3_func_decl, Z3_app, Z3_pattern are
       Z3_ast's.
 
       After a context is created, the configuration cannot be changed.
       All main interaction with Z3 happens in the context of a \c Z3_context.
    */
    Z3_context Z3_API Z3_mk_context_rc(__in Z3_config c);

    /**
       \brief Set the SMTLIB logic to be used in the given logical context.
       It is incorrect to invoke this function after invoking
       #Z3_check, #Z3_check_and_get_model, #Z3_check_assumptions and #Z3_push.
       Return \c Z3_TRUE if the logic was changed successfully, and \c Z3_FALSE otherwise.
    */
    Z3_bool Z3_API Z3_set_logic(__in Z3_context c, __in_z Z3_string logic);
    
    /**
       \brief Delete the given logical context.

       \sa Z3_mk_config
    */
    void Z3_API Z3_del_context(__in Z3_context c);
    
    /**
       \brief Increment the reference counter of the given AST.
       The context \c c should have been created using #Z3_mk_context_rc.
       This function is a NOOP if \c c was created using #Z3_mk_context.
    */
    void Z3_API Z3_inc_ref(__in Z3_context c, __in Z3_ast a);

    /**
       \brief Decrement the reference counter of the given AST.
       The context \c c should have been created using #Z3_mk_context_rc.
       This function is a NOOP if \c c was created using #Z3_mk_context.
    */
    void Z3_API Z3_dec_ref(__in Z3_context c, __in Z3_ast a);

    /**
       \brief Enable trace messages to a file

       When trace messages are enabled, Z3 will record the operations performed on a context in the given file file.
       Return \c Z3_TRUE if the file was opened successfully, and \c Z3_FALSE otherwise.

       \sa Z3_trace_off
    */
    Z3_bool Z3_API Z3_trace_to_file(__in Z3_context c, __in_z Z3_string trace_file);

    /**
       \brief Enable trace messages to a standard error.

       \sa Z3_trace_off
    */
    void Z3_API Z3_trace_to_stderr(__in Z3_context c);

    /**
       \brief Enable trace messages to a standard output.

       \sa Z3_trace_off
    */
    void Z3_API Z3_trace_to_stdout(__in Z3_context c);

    /**
       \brief Disable trace messages.

       \sa Z3_trace_to_file
       \sa Z3_trace_to_stdout
       \sa Z3_trace_to_stderr
    */
    void Z3_API Z3_trace_off(__in Z3_context c);

    /**
       \brief Enable/disable printing warning messages to the console.

       Warnings are printed after passing \c true, warning messages are
       suppressed after calling this method with \c false.       
    */
    void Z3_API Z3_toggle_warning_messages(__in Z3_bool enabled);

    /**
       \brief Update a mutable configuration parameter.

       The list of all configuration parameters can be obtained using the Z3 executable:

       \verbatim
       z3.exe -ini?
       \endverbatim

       Only a few configuration parameters are mutable once the context is created.
       The error handler is invoked when trying to modify an immutable parameter.

       \sa Z3_set_param_value
    */
    void Z3_API Z3_update_param_value(__in Z3_context c, __in_z Z3_string param_id, __in_z Z3_string param_value);

    /**
       \brief Get a configuration parameter.
      
       Returns false if the parameter value does not exist.

       \sa Z3_mk_config
       \sa Z3_set_param_value
    */

#ifndef CAMLIDL
    Z3_bool Z3_API Z3_get_param_value(__in Z3_context c, __in_z Z3_string param_id, __out_z Z3_string_ptr param_value);
#endif

    /*@}*/

    /**
       @name Symbols
    */
    /*@{*/
    /**
       \brief Create a Z3 symbol using an integer.

       Symbols are used to name several term and type constructors.

       NB. Not all integers can be passed to this function.
       The legal range of unsigned integers is 0 to 2^30-1.

       \sa Z3_mk_string_symbol
    */
    Z3_symbol Z3_API Z3_mk_int_symbol(__in Z3_context c, __in int i);

    /**
       \brief Create a Z3 symbol using a C string.

       Symbols are used to name several term and type constructors.

       \sa Z3_mk_int_symbol
    */
    Z3_symbol Z3_API Z3_mk_string_symbol(__in Z3_context c, __in_z Z3_string s);
    /*@}*/
    
    
    /**
       @name Sorts
    */
    /*@{*/
    
    /**
       \brief compare sorts.
    */
    Z3_bool Z3_API Z3_is_eq_sort(__in Z3_context c, __in Z3_sort s1, __in Z3_sort s2);

    /**
       \brief Create a free (uninterpreted) type using the given name (symbol).
       
       Two free types are considered the same iff the have the same name.
    */
    Z3_sort Z3_API Z3_mk_uninterpreted_sort(__in Z3_context c, __in Z3_symbol s);
    

    /**
       \brief Create the Boolean type. 

       This type is used to create propositional variables and predicates.
    */
    Z3_sort Z3_API Z3_mk_bool_sort(__in Z3_context c);
    
    /**
       \brief Create an integer type.

       This type is not the int type found in programming languages.
       A machine integer can be represented using bit-vectors. The function
       #Z3_mk_bv_sort creates a bit-vector type.

       \sa Z3_mk_bv_sort
    */
    Z3_sort Z3_API Z3_mk_int_sort(__in Z3_context c);
    
    /**
       \brief Create a real type. 

       This type is not a floating point number.
       Z3 does not have support for floating point numbers yet.
    */
    Z3_sort Z3_API Z3_mk_real_sort(__in Z3_context c);

    /**
       \brief Create a bit-vector type of the given size.
    
       This type can also be seen as a machine integer.

       \remark The size of the bitvector type must be greater than zero.
    */
    Z3_sort Z3_API Z3_mk_bv_sort(__in Z3_context c, __in unsigned sz);

    /**
       \brief Create an array type. 
       
       We usually represent the array type as: <tt>[domain -> range]</tt>.
       Arrays are usually used to model the heap/memory in software verification.

       \sa Z3_mk_select
       \sa Z3_mk_store
    */
    Z3_sort Z3_API Z3_mk_array_sort(__in Z3_context c, __in Z3_sort domain, __in Z3_sort range);

    /**
       \brief Create a tuple type.
       
       \mlonly [mk_tuple_sort c name field_names field_sorts] creates a tuple with a constructor named [name],
       a [n] fields, where [n] is the size of the arrays [field_names] and [field_sorts].
       \endmlonly

       \conly A tuple with \c n fields has a constructor and \c n projections.
       \conly This function will also declare the constructor and projection functions.

       \param c logical context
       \param mk_tuple_name name of the constructor function associated with the tuple type.
       \param num_fields number of fields in the tuple type.
       \param field_names name of the projection functions.
       \param field_sorts type of the tuple fields.
       \param mk_tuple_decl output parameter that will contain the constructor declaration.
       \param proj_decl output parameter that will contain the projection function declarations. This field must be a buffer of size \c num_fields allocated by the user.
    */
    Z3_sort Z3_API Z3_mk_tuple_sort(__in Z3_context c, 
                                        __in Z3_symbol mk_tuple_name, 
                                        __in unsigned num_fields, 
                                        __in_ecount(num_fields) Z3_symbol   const field_names[],
                                        __in_ecount(num_fields) Z3_sort const field_sorts[],
                                        __out Z3_func_decl * mk_tuple_decl,
                                        __out_ecount(num_fields)  Z3_func_decl proj_decl[]);

    /**
       \brief Create a enumeration sort.
       
       \mlonly [mk_enumeration_sort c enums] creates an enumeration sort with enumeration names [enums], 
               it also returns [n] predicates, where [n] is the number of [enums] corresponding
               to testing whether an element is one of the enumerants.
       \endmlonly

       \conly An enumeration sort with \c n elements.
       \conly This function will also declare the functions corresponding to the enumerations.

       \param c logical context
       \param name name of the enumeration sort.
       \param n number of elemenets in enumeration sort.
       \param enum_names names of the enumerated elements.
       \param enum_consts constants corresponding to the enumerated elements.
       \param enum_testers predicates testing if terms of the enumeration sort correspond to an enumeration.
    */
    Z3_sort Z3_API Z3_mk_enumeration_sort(__in Z3_context c, 
                                          __in Z3_symbol name,
                                          __in unsigned n,
                                          __in_ecount(n)  Z3_symbol  const enum_names[],
                                          __out_ecount(n) Z3_func_decl enum_consts[],
                                          __out_ecount(n) Z3_func_decl enum_testers[]);

    /**
       \brief Create a list sort
       
       \mlonly [mk_list_sort c name elem_sort] creates a list sort of [name], over elements of sort [elem_sort].
       \endmlonly

       \conly A list sort over \c elem_sort 
       \conly This function declares the corresponding constructors and testers for lists.

       \param c logical context
       \param name name of the list sort.
       \param elem_sort sort of list elements.
       \param nil_decl declaration for the empty list.
       \param is_nil_decl test for the empty list.
       \param cons_decl declaration for a cons cell.
       \param is_cons_decl cons cell test.
       \param head_decl list head.
       \param tail_decl list tail.
    */

    Z3_sort Z3_API Z3_mk_list_sort(__in Z3_context c,
                                   __in Z3_symbol name,
                                   __in Z3_sort   elem_sort,
                                   __out Z3_func_decl* nil_decl,
                                   __out Z3_func_decl* is_nil_decl,
                                   __out Z3_func_decl* cons_decl,
                                   __out Z3_func_decl* is_cons_decl,
                                   __out Z3_func_decl* head_decl,
                                   __out Z3_func_decl* tail_decl
                                   );

    /**
       \brief Create a constructor.
       
       \param c logical context.
       \param name constructor name.
       \param recognizer name of recognizer function.
       \param num_fields number of fields in constructor.
       \param field_names names of the constructor fields.
       \param sorts field sorts, 0 if the field sort refers to a recursive sort.
       \param sort_refs reference to datatype sort that is an argument to the constructor; if the corresponding
                        sort reference is 0, then the value in sort_refs should be an index referring to 
                        one of the recursive datatypes that is declared.                        
    */

    Z3_constructor Z3_API Z3_mk_constructor(__in Z3_context c,
                                            __in Z3_symbol name,
                                            __in Z3_symbol recognizer,
                                            __in unsigned num_fields,
                                            __in_ecount(num_fields) Z3_symbol const field_names[],
                                            __in_ecount(num_fields) Z3_sort const sorts[],
                                            __in_ecount(num_fields) unsigned sort_refs[]
                                            );

    /**
       \brief Query constructor for declared funcions.
       
       \param c logical context.
       \param constr constructor container. The container must have been passed in to a #Z3_mk_datatype call.
       \param num_fields number of accessor fields in the constructor.
       \param constructor constructor function declaration.
       \param tester constructor test function declaration.
       \param accessors array of accessor function declarations.
    */

    void Z3_API Z3_query_constructor(__in Z3_context c,
                                     __in Z3_constructor constr,
                                     __in unsigned num_fields,
                                     __out Z3_func_decl* constructor,
                                     __out Z3_func_decl* tester,
                                     __out_ecount(num_fields) Z3_func_decl accessors[]);
    
    /**
       \brief Reclaim memory allocated to constructor.

       \param c logical context.
       \param constr constructor.
    */
       
    void Z3_API Z3_del_constructor(__in Z3_context c, __in Z3_constructor constr);

    /**
       \brief Create recursive datatype. Return the datatype sort.

       \param c logical context.
	   \param name name of datatype.
       \param num_constructors number of constructors passed in.
       \param constructors array of constructor containers.
    */

    Z3_sort Z3_API Z3_mk_datatype(__in Z3_context c,
                                  __in Z3_symbol name,
                                  __in unsigned num_constructors,
                                  __inout_ecount(num_constructors) Z3_constructor constructors[]);


    /**
       \brief Create list of constructors.

       \param c logical context.
       \param num_constructors number of constructors in list.
       \param constructors list of constructors.
    */

    Z3_constructor_list Z3_API Z3_mk_constructor_list(__in Z3_context c,
                                                      __in unsigned num_constructors,
                                                      __in_ecount(num_constructors) Z3_constructor constructors[]);

    /**
       \brief reclaim memory allocated for constructor list.

       Each constructor inside the constructor list must be independently reclaimed using #Z3_del_constructor.

       \param c logical context.
       \param clist constructor list container.

    */

    void Z3_API Z3_del_constructor_list(__in Z3_context c, __in Z3_constructor_list clist);
                                        
    /**
       \brief Create mutually recursive datatypes.

       \param c logical context.
       \param num_sorts number of datatype sorts.
       \param sort_names names of datatype sorts.
       \param sorts array of datattype sorts.
       \param constructor_lists list of constructors, one list per sort.
    */

    void Z3_API Z3_mk_datatypes(__in Z3_context c,
                                __in unsigned num_sorts,
                                __in_ecount(num_sorts) Z3_symbol sort_names[],
                                __out_ecount(num_sorts) Z3_sort sorts[],
                                __inout_ecount(num_sorts) Z3_constructor_list constructor_lists[]);
    
    /*@}*/




    /**
       @name Injective functions
    */
    /*@{*/
    

    /**
       \brief Create injective function declaration
    */
    Z3_func_decl Z3_API Z3_mk_injective_function(
        __in Z3_context c, 
        __in Z3_symbol s, 
        unsigned domain_size, __in_ecount(domain_size) Z3_sort const domain[],
        __in Z3_sort range
        );

    /*@}*/

    /**
       @name Constants and Applications
     */
    /*@{*/

    /**
       \brief compare terms.
    */
    Z3_bool Z3_API Z3_is_eq_ast(__in Z3_context c, __in Z3_ast t1, Z3_ast t2);


    /**
       \brief compare terms.
    */
    Z3_bool Z3_API Z3_is_eq_func_decl(__in Z3_context c, __in Z3_func_decl f1, Z3_func_decl f2);


    /**
       \brief Declare a constant or function.

       \mlonly [mk_func_decl c n d r] creates a function with name [n], domain [d], and range [r].
       The arity of the function is the size of the array [d]. \endmlonly

       \param c logical context.
       \param s name of the constant or function.
       \param domain_size number of arguments. It is 0 when declaring a constant.
       \param domain array containing the sort of each argument. The array must contain domain_size elements. It is 0 whe declaring a constant.
       \param range sort of the constant or the return sort of the function.

       After declaring a constant or function, the function
       #Z3_mk_app can be used to create a constant or function
       application.

       \sa Z3_mk_app
    */
    Z3_func_decl Z3_API Z3_mk_func_decl(__in Z3_context c, __in Z3_symbol s,
                                        __in unsigned domain_size, __in_ecount(domain_size) Z3_sort const domain[],
                                        __in Z3_sort range);

    
    /**
       \brief Create a constant or function application.

       \sa Z3_mk_func_decl
    */
    Z3_ast Z3_API Z3_mk_app(
        __in Z3_context c, 
        __in Z3_func_decl d,
        __in unsigned num_args, 
        __in_ecount(num_args) Z3_ast const args[]);

    /**
       \brief Declare and create a constant.
       
       \conly This function is a shorthand for:
       \conly \code
       \conly Z3_func_decl d = Z3_mk_func_decl(c, s, 0, 0, ty);
       \conly Z3_ast n            = Z3_mk_app(c, d, 0, 0);
       \conly \endcode
       
       \mlonly [mk_const c s t] is a shorthand for [mk_app c (mk_func_decl c s [||] t) [||]] \endmlonly

       \sa Z3_mk_func_decl
       \sa Z3_mk_app
    */
    Z3_ast Z3_API Z3_mk_const(__in Z3_context c, __in Z3_symbol s, __in Z3_sort ty);

    /**
       \brief Create a labeled formula.

       \param c logical context.
       \param s name of the label.
       \param is_pos label polarity.
       \param f formula being labeled.

       A label behaves as an identity function, so the truth value of the 
       labeled formula is unchanged. Labels are used for identifying 
       useful sub-formulas when generating counter-examples.
    */
    Z3_ast Z3_API Z3_mk_label(__in Z3_context c, __in Z3_symbol s, Z3_bool is_pos, Z3_ast f);

    /**
       \brief Declare a fresh constant or function.

       Z3 will generate an unique name for this function declaration.
       \conly If prefix is different from \c NULL, then the name generate by Z3 will start with \c prefix.
       
       \conly \remark If \c prefix is NULL, then it is assumed to be the empty string.

       \sa Z3_mk_func_decl
    */
    Z3_func_decl Z3_API Z3_mk_fresh_func_decl(__in Z3_context c, __in_z Z3_string prefix,
                                                   __in unsigned domain_size, __in_ecount(domain_size) Z3_sort const domain[],
                                                   __in Z3_sort range);
    
    /**
       \brief Declare and create a fresh constant.
       
       \conly This function is a shorthand for:
       \conly \code Z3_func_decl d = Z3_mk_fresh_func_decl(c, prefix, 0, 0, ty); Z3_ast n = Z3_mk_app(c, d, 0, 0); \endcode

       \mlonly [mk_fresh_const c p t] is a shorthand for [mk_app c (mk_fresh_func_decl c p [||] t) [||]]. \endmlonly

       \conly \remark If \c prefix is NULL, then it is assumed to be the empty string.
       
       \sa Z3_mk_func_decl
       \sa Z3_mk_app
    */
    Z3_ast Z3_API Z3_mk_fresh_const(__in Z3_context c, __in_z Z3_string prefix, __in Z3_sort ty);

    
    /** 
        \brief Create an AST node representing \c true.
    */
    Z3_ast Z3_API Z3_mk_true(__in Z3_context c);

    /** 
        \brief Create an AST node representing \c false.
    */
    Z3_ast Z3_API Z3_mk_false(__in Z3_context c);
    
    /** 
        \brief \mlh mk_eq c l r \endmlh
        Create an AST node representing <tt>l = r</tt>.
        
        The nodes \c l and \c r must have the same type. 
    */
    Z3_ast Z3_API Z3_mk_eq(__in Z3_context c, __in Z3_ast l, __in Z3_ast r);
    
    /**
       \conly \brief Create an AST node representing <tt>distinct(args[0], ..., args[num_args-1])</tt>.
       \mlonly \brief \[ [mk_distinct c [| t_1; ...; t_n |]] \] Create an AST
       node represeting a distinct construct. It is used for declaring
       the arguments t_i pairwise distinct. \endmlonly

       \conly The \c distinct construct is used for declaring the arguments pairwise distinct. 
       \conly That is, <tt>Forall 0 <= i < j < num_args. not args[i] = args[j]</tt>.
       
       All arguments must have the same sort.

       \remark The number of arguments of a distinct construct must be greater than one.
    */
    Z3_ast Z3_API Z3_mk_distinct(__in Z3_context c, __in unsigned num_args, __in_ecount(num_args) Z3_ast const args[]);

    /** 
        \brief \mlh mk_not c a \endmlh 
        Create an AST node representing <tt>not(a)</tt>.
        
        The node \c a must have Boolean sort.
    */
    Z3_ast Z3_API Z3_mk_not(__in Z3_context c, __in Z3_ast a);
    
    /**
       \brief \mlh mk_ite c t1 t2 t2 \endmlh 
       Create an AST node representing an if-then-else: <tt>ite(t1, t2,
       t3)</tt>.

       The node \c t1 must have Boolean sort, \c t2 and \c t3 must have the same sort.
       The sort of the new node is equal to the sort of \c t2 and \c t3.
    */
    Z3_ast Z3_API Z3_mk_ite(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2, __in Z3_ast t3);

    /**
       \brief \mlh mk_iff c t1 t2 \endmlh
       Create an AST node representing <tt>t1 iff t2</tt>.

       The nodes \c t1 and \c t2 must have Boolean sort.
    */
    Z3_ast Z3_API Z3_mk_iff(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_implies c t1 t2 \endmlh
       Create an AST node representing <tt>t1 implies t2</tt>.

       The nodes \c t1 and \c t2 must have Boolean sort.
    */
    Z3_ast Z3_API Z3_mk_implies(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
    
    /**
       \brief \mlh mk_xor c t1 t2 \endmlh
       Create an AST node representing <tt>t1 xor t2</tt>.

       The nodes \c t1 and \c t2 must have Boolean sort.
    */
    Z3_ast Z3_API Z3_mk_xor(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
    
    /**
       \conly \brief Create an AST node representing <tt>args[0] and ... and args[num_args-1]</tt>.
       \mlonly \brief \[ [mk_and c [| t_1; ...; t_n |]] \] Create the conjunction: {e t_1 and ... and t_n}. \endmlonly

       \conly The array \c args must have \c num_args elements. 
       All arguments must have Boolean sort.
       
       \remark The number of arguments must be greater than zero.
    */
    Z3_ast Z3_API Z3_mk_and(__in Z3_context c, __in unsigned num_args, __in_ecount(num_args) Z3_ast const args[]);
    
    /**
       \conly \brief Create an AST node representing <tt>args[0] or ... or args[num_args-1]</tt>.
       \mlonly \brief \[ [mk_or c [| t_1; ...; t_n |]] \] Create the disjunction: {e t_1 or ... or t_n}. \endmlonly

       \conly The array \c args must have \c num_args elements. 
       All arguments must have Boolean sort.

       \remark The number of arguments must be greater than zero.
    */
    Z3_ast Z3_API Z3_mk_or(__in Z3_context c, __in unsigned num_args, __in_ecount(num_args) Z3_ast const args[]);
    
    /**
       \conly \brief Create an AST node representing <tt>args[0] + ... + args[num_args-1]</tt>.
       \mlonly \brief \[ [mk_add c [| t_1; ...; t_n |]] \] Create the term: {e t_1 + ... + t_n}. \endmlonly

       \conly The array \c args must have \c num_args elements. 
       All arguments must have int or real sort.

       \remark The number of arguments must be greater than zero.
    */
    Z3_ast Z3_API Z3_mk_add(__in Z3_context c, __in unsigned num_args, __in_ecount(num_args) Z3_ast const args[]);
    
    /**
       \conly \brief Create an AST node representing <tt>args[0] * ... * args[num_args-1]</tt>.
       \mlonly \brief \[ [mk_mul c [| t_1; ...; t_n |]] \] Create the term: {e t_1 * ... * t_n}. \endmlonly

       \conly The array \c args must have \c num_args elements. 
       All arguments must have int or real sort.
       
       \remark Z3 has limited support for non-linear arithmetic.
       \remark The number of arguments must be greater than zero.
    */
    Z3_ast Z3_API Z3_mk_mul(__in Z3_context c, __in unsigned num_args, __in_ecount(num_args) Z3_ast const args[]);
    
    /**
       \conly \brief Create an AST node representing <tt>args[0] - ... - args[num_args - 1]</tt>.
       \mlonly \brief \[ [mk_sub c [| t_1; ...; t_n |]] \] Create the term: {e t_1 - ... - t_n}. \endmlonly

       \conly The array \c args must have \c num_args elements. 
       All arguments must have int or real sort.

       \remark The number of arguments must be greater than zero.
    */
    Z3_ast Z3_API Z3_mk_sub(__in Z3_context c, __in unsigned num_args, __in_ecount(num_args) Z3_ast const args[]);

    /**
       \conly \brief Create an AST node representing <tt>-arg</tt>.
       \mlonly \brief \[ [mk_unary_minus c arg] \] Create the term: {e - arg}. \endmlonly

       The argument must have int or real type.

    */
    Z3_ast Z3_API Z3_mk_unary_minus(__in Z3_context c, __in Z3_ast arg);


    /**
       \conly \brief Create an AST node representing <tt>arg1 div arg2</tt>.
       \mlonly \brief \[ [mk_div c t_1 t_2] \] Create the term: {e t_1 div t_2}. \endmlonly

       The arguments must either both have int type or both have real type.
       If the arguments have int type, then the result type is an int type, otherwise the
       the result type is real.

    */
    Z3_ast Z3_API Z3_mk_div(__in Z3_context c, __in Z3_ast arg1, __in Z3_ast arg2);


    /**
       \conly \brief Create an AST node representing <tt>arg1 mod arg2</tt>.
       \mlonly \brief \[ [mk_mod c t_1 t_2] \] Create the term: {e t_1 mod t_2}. \endmlonly

       The arguments must have int type.

    */
    Z3_ast Z3_API Z3_mk_mod(__in Z3_context c, __in Z3_ast arg1, __in Z3_ast arg2);

    /**
       \conly \brief Create an AST node representing <tt>arg1 rem arg2</tt>.
       \mlonly \brief \[ [mk_rem c t_1 t_2] \] Create the term: {e t_1 rem t_2}. \endmlonly

       The arguments must have int type.

    */
    Z3_ast Z3_API Z3_mk_rem(__in Z3_context c, __in Z3_ast arg1, __in Z3_ast arg2);

    /** 
        \brief \mlh mk_lt c t1 t2 \endmlh 
        Create less than.

        The nodes \c t1 and \c t2 must have the same sort, and must be int or real.
    */
    Z3_ast Z3_API Z3_mk_lt(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /** 
        \brief \mlh mk_le c t1 t2 \endmlh
        Create less than or equal to.
        
        The nodes \c t1 and \c t2 must have the same sort, and must be int or real.
    */
    Z3_ast Z3_API Z3_mk_le(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /** 
        \brief \mlh mk_gt c t1 t2 \endmlh
        Create greater than.
        
        The nodes \c t1 and \c t2 must have the same sort, and must be int or real.
    */
    Z3_ast Z3_API Z3_mk_gt(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /** 
        \brief \mlh mk_ge c t1 t2 \endmlh
        Create greater than or equal to.
        
        The nodes \c t1 and \c t2 must have the same sort, and must be int or real.
    */
    Z3_ast Z3_API Z3_mk_ge(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /** 
        \brief \mlh mk_int2real c t1 \endmlh
        Coerce an integer to a real.

        There is also a converse operation exposed.
        It follows the semantics prescribed by the SMT-LIB standard.

        You can take the floor of a real by 
        creating an auxiliary integer constant \c k and
        and asserting <tt> mk_int2real(k) <= t1 < mk_int2real(k)+1</tt>.
        
        The node \c t1 must have sort integer.

        \sa Z3_mk_real2int
        \sa Z3_mk_is_int
    */
    Z3_ast Z3_API Z3_mk_int2real(__in Z3_context c, __in Z3_ast t1);

    /** 
        \brief \mlh mk_real2int c t1 \endmlh
        Coerce a real to an integer.

        The semantics of this function follows the SMT-LIB standard
        for the function to_int

        \sa Z3_mk_int2real
        \sa Z3_mk_is_int
    */
    Z3_ast Z3_API Z3_mk_real2int(__in Z3_context c, __in Z3_ast t1);

    /** 
        \brief \mlh mk_is_int c t1 \endmlh
        Check if a real number is an integer.

        \sa Z3_mk_int2real
        \sa Z3_mk_real2int
    */
    Z3_ast Z3_API Z3_mk_is_int(__in Z3_context c, __in Z3_ast t1);

    /**
       \brief \mlh mk_bvnot c t1 \endmlh
       Bitwise negation.

       The node \c t1 must have a bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvnot(__in Z3_context c, __in Z3_ast t1);

    /**
       \brief \mlh mk_bvredand c t1 \endmlh
       Take conjunction of bits in vector, return vector of length 1.

       The node \c t1 must have a bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvredand(__in Z3_context c, __in Z3_ast t1);

    /**
       \brief \mlh mk_bvredor c t1 \endmlh
       Take disjunction of bits in vector, return vector of length 1.

       The node \c t1 must have a bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvredor(__in Z3_context c, __in Z3_ast t1);

    /**
       \brief \mlh mk_bvand c t1 t2 \endmlh
       Bitwise and.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvand(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvor c t1 t2 \endmlh
       Bitwise or.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvor(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvxor c t1 t2 \endmlh
       Bitwise exclusive-or.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvxor(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvnand c t1 t2 \endmlh
       Bitwise nand. 

       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvnand(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvnor c t1 t2 \endmlh
       Bitwise nor. 

       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvnor(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvxnor c t1 t2 \endmlh
       Bitwise xnor. 
       
       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvxnor(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvneg c t1 \endmlh
       Standard two's complement unary minus. 

       The node \c t1 must have bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvneg(__in Z3_context c, __in Z3_ast t1);
    
    /** 
        \brief \mlh mk_bvadd c t1 t2 \endmlh
        Standard two's complement addition.
        
        The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvadd(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /** 
        \brief \mlh mk_bvsub c t1 t2 \endmlh
        Standard two's complement subtraction.
        
        The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvsub(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
    
    /** 
        \brief \mlh mk_bvmul c t1 t2 \endmlh
        Standard two's complement multiplication.
        
        The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvmul(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /** 
        \brief \mlh mk_bvudiv c t1 t2 \endmlh
        Unsigned division. 

        It is defined as the \c floor of <tt>t1/t2</tt> if \c t2 is
        different from zero. If <tt>t2</tt> is zero, then the result
        is undefined.
        
        The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvudiv(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /** 
        \brief \mlh mk_bvsdiv c t1 t2 \endmlh
        Two's complement signed division. 

        It is defined in the following way:

        - The \c floor of <tt>t1/t2</tt> if \c t2 is different from zero, and <tt>t1*t2 >= 0</tt>.

        - The \c ceiling of <tt>t1/t2</tt> if \c t2 is different from zero, and <tt>t1*t2 < 0</tt>.
        
        If <tt>t2</tt> is zero, then the result is undefined.
        
        The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvsdiv(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvurem c t1 t2 \endmlh
       Unsigned remainder.

       It is defined as <tt>t1 - (t1 /u t2) * t2</tt>, where <tt>/u</tt> represents unsigned division.
       
       If <tt>t2</tt> is zero, then the result is undefined.
       
       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvurem(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvsrem c t1 t2 \endmlh
       Two's complement signed remainder (sign follows dividend).

       It is defined as <tt>t1 - (t1 /s t2) * t2</tt>, where <tt>/s</tt> represents signed division.
       The most significant bit (sign) of the result is equal to the most significant bit of \c t1.

       If <tt>t2</tt> is zero, then the result is undefined.
       
       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       \sa Z3_mk_bvsmod
    */
    Z3_ast Z3_API Z3_mk_bvsrem(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvsmod c t1 t2 \endmlh
       Two's complement signed remainder (sign follows divisor).
       
       If <tt>t2</tt> is zero, then the result is undefined.
       
       The nodes \c t1 and \c t2 must have the same bit-vector sort.

       \sa Z3_mk_bvsrem
    */
    Z3_ast Z3_API Z3_mk_bvsmod(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvult c t1 t2 \endmlh
       Unsigned less than.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvult(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
    
    /**
       \brief \mlh mk_bvslt c t1 t2 \endmlh
       Two's complement signed less than.
       
       It abbreviates:
       \code
      (or (and (= (extract[|m-1|:|m-1|] t1) bit1)
               (= (extract[|m-1|:|m-1|] t2) bit0))
          (and (= (extract[|m-1|:|m-1|] t1) (extract[|m-1|:|m-1|] t2))
               (bvult t1 t2)))
       \endcode

       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvslt(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvule c t1 t2 \endmlh
       Unsigned less than or equal to.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvule(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvsle c t1 t2 \endmlh
       Two's complement signed less than or equal to.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvsle(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvuge c t1 t2 \endmlh
       Unsigned greater than or equal to.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvuge(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvsge c t1 t2 \endmlh
       Two's complement signed greater than or equal to.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvsge(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvugt c t1 t2 \endmlh
       Unsigned greater than.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvugt(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvsgt c t1 t2 \endmlh
       Two's complement signed greater than.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvsgt(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_concat c t1 t2 \endmlh
       Concatenate the given bit-vectors.
       
       The nodes \c t1 and \c t2 must have (possibly different) bit-vector sorts

       The result is a bit-vector of size <tt>n1+n2</tt>, where \c n1 (\c n2) is the size
       of \c t1 (\c t2).
    */
    Z3_ast Z3_API Z3_mk_concat(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
    
    /**
       \brief \mlh mk_extract c high low t1 \endmlh
       Extract the bits \c high down to \c low from a bitvector of
       size \c m to yield a new bitvector of size \c n, where <tt>n =
       high - low + 1</tt>.

       The node \c t1 must have a bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_extract(__in Z3_context c, __in unsigned high, __in unsigned low, __in Z3_ast t1);

    /**
       \brief \mlh mk_sign_ext c i t1 \endmlh
       Sign-extend of the given bit-vector to the (signed) equivalent bitvector of
       size <tt>m+i</tt>, where \c m is the size of the given
       bit-vector.

       The node \c t1 must have a bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_sign_ext(__in Z3_context c, __in unsigned i, __in Z3_ast t1);

    /**
       \brief \mlh mk_zero_ext c i t1 \endmlh
       Extend the given bit-vector with zeros to the (unsigned) equivalent
       bitvector of size <tt>m+i</tt>, where \c m is the size of the
       given bit-vector.
       
       The node \c t1 must have a bit-vector sort. 
    */
    Z3_ast Z3_API Z3_mk_zero_ext(__in Z3_context c, __in unsigned i, __in Z3_ast t1);

    /**
       \brief \mlh mk_repeat c i t1 \endmlh
       Repeat the given bit-vector up length <tt>i</tt>.
       
       The node \c t1 must have a bit-vector sort. 
    */
    Z3_ast Z3_API Z3_mk_repeat(__in Z3_context c, __in unsigned i, __in Z3_ast t1);

    /**
       \brief \mlh mk_bvshl c t1 t2 \endmlh
       Shift left.

       It is equivalent to multiplication by <tt>2^x</tt> where \c x is the value of the
       third argument.

       NB. The semantics of shift operations varies between environments. This 
       definition does not necessarily capture directly the semantics of the 
       programming language or assembly architecture you are modeling.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvshl(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvlshr c t1 t2 \endmlh
       Logical shift right.

       It is equivalent to unsigned division by <tt>2^x</tt> where \c x is the
       value of the third argument.

       NB. The semantics of shift operations varies between environments. This 
       definition does not necessarily capture directly the semantics of the 
       programming language or assembly architecture you are modeling.

       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvlshr(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvashr c t1 t2 \endmlh
       Arithmetic shift right.
       
       It is like logical shift right except that the most significant
       bits of the result always copy the most significant bit of the
       second argument.

       NB. The semantics of shift operations varies between environments. This 
       definition does not necessarily capture directly the semantics of the 
       programming language or assembly architecture you are modeling.
       
       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvashr(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
    
    /**
       \brief \mlh mk_rotate_left c i t1 \endmlh
       Rotate bits of \c t1 to the left \c i times.
       
       The node \c t1 must have a bit-vector sort. 
    */
    Z3_ast Z3_API Z3_mk_rotate_left(__in Z3_context c, __in unsigned i, __in Z3_ast t1);
    
    /**
       \brief \mlh mk_rotate_right c i t1 \endmlh
       Rotate bits of \c t1 to the right \c i times.
       
       The node \c t1 must have a bit-vector sort. 
    */
    Z3_ast Z3_API Z3_mk_rotate_right(__in Z3_context c, __in unsigned i, __in Z3_ast t1);

    /**
       \brief \mlh mk_ext_rotate_left c t1 t2 \endmlh
       Rotate bits of \c t1 to the left \c t2 times.
       
       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_ext_rotate_left(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_ext_rotate_right c t1 t2 \endmlh
       Rotate bits of \c t1 to the right \c t2 times.
       
       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_ext_rotate_right(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
    
    /**
       \brief \mlh mk_int2bv c n t1 \endmlh
       Create an \c n bit bit-vector from the integer argument \c t1.

       NB. This function is essentially treated as uninterpreted. 
       So you cannot expect Z3 to precisely reflect the semantics of this function
       when solving constraints with this function.
       
       The node \c t1 must have integer sort. 
    */
    Z3_ast Z3_API Z3_mk_int2bv(__in Z3_context c, __in unsigned n, __in Z3_ast t1);

    /**
       \brief \mlh mk_bv2int c t1 is_signed \endmlh
       Create an integer from the bit-vector argument \c t1.
       If \c is_signed is false, then the bit-vector \c t1 is treated as unsigned. 
       So the result is non-negative
       and in the range <tt>[0..2^N-1]</tt>, where N are the number of bits in \c t1.
       If \c is_signed is true, \c t1 is treated as a signed bit-vector.

       NB. This function is essentially treated as uninterpreted. 
       So you cannot expect Z3 to precisely reflect the semantics of this function
       when solving constraints with this function.

       The node \c t1 must have a bit-vector sort. 
    */
    Z3_ast Z3_API Z3_mk_bv2int(__in Z3_context c,__in Z3_ast t1, Z3_bool is_signed);

    /**
       \brief \mlh mk_bvadd_no_overflow c t1 t2 is_signed \endmlh
       Create a predicate that checks that the bit-wise addition
       of \c t1 and \c t2 does not overflow.
       
       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvadd_no_overflow(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2, Z3_bool is_signed);

    /**
       \brief \mlh mk_bvadd_no_underflow c t1 t2 \endmlh
       Create a predicate that checks that the bit-wise signed addition
       of \c t1 and \c t2 does not underflow.
       
       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvadd_no_underflow(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvsub_no_overflow c t1 t2 \endmlh
       Create a predicate that checks that the bit-wise signed subtraction
       of \c t1 and \c t2 does not overflow.
       
       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvsub_no_overflow(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvsub_no_underflow c t1 t2 is_signed \endmlh
       Create a predicate that checks that the bit-wise subtraction
       of \c t1 and \c t2 does not underflow.
       
       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvsub_no_underflow(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2, Z3_bool is_signed);

    /**
       \brief \mlh mk_bvsdiv_no_overflow c t1 t2 \endmlh
       Create a predicate that checks that the bit-wise signed division 
       of \c t1 and \c t2 does not overflow.
       
       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvsdiv_no_overflow(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_bvneg_no_overflow c t1 \endmlh
       Check that bit-wise negation does not overflow when 
       \c t1 is interpreted as a signed bit-vector.
       
       The node \c t1 must have bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvneg_no_overflow(__in Z3_context c, __in Z3_ast t1);

    /**
       \brief \mlh mk_bvmul_no_overflow c t1 t2 is_signed \endmlh
       Create a predicate that checks that the bit-wise multiplication
       of \c t1 and \c t2 does not overflow.
       
       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvmul_no_overflow(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2, Z3_bool is_signed);

    /**
       \brief \mlh mk_bvmul_no_underflow c t1 t2 \endmlh
       Create a predicate that checks that the bit-wise signed multiplication
       of \c t1 and \c t2 does not underflow.
       
       The nodes \c t1 and \c t2 must have the same bit-vector sort.
    */
    Z3_ast Z3_API Z3_mk_bvmul_no_underflow(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
       \brief \mlh mk_select c a i \endmlh
       Array read.

       The node \c a must have an array sort <tt>[domain -> range]</tt>, and \c i must have the sort \c domain.
       The sort of the result is \c range.

       \sa Z3_mk_array_sort
       \sa Z3_mk_store
    */
    Z3_ast Z3_API Z3_mk_select(__in Z3_context c, __in Z3_ast a, __in Z3_ast i);
    
    /**
       \brief \mlh mk_store c a i v \endmlh
       Array update.
       
       The node \c a must have an array sort <tt>[domain -> range]</tt>, \c i must have sort \c domain,
       \c v must have sort range. The sort of the result is <tt>[domain -> range]</tt>.
       
       \sa Z3_mk_array_sort
       \sa Z3_mk_select
    */
    Z3_ast Z3_API Z3_mk_store(__in Z3_context c, __in Z3_ast a, __in Z3_ast i, __in Z3_ast v);

    /** 
        \brief Create the constant array.

        \param c logical context.
        \param domain domain sort for the array.
        \param v value that the array maps to.
    */
    Z3_ast Z3_API Z3_mk_const_array(__in Z3_context c, __in Z3_sort domain, __in Z3_ast v);

    /**
       \brief \mlh mk_map f n args \endmlh
       map f on the the argument arrays.
       
       The \c n nodes \c args must be of array sorts <tt>[domain_i -> range_i]</tt>.
       The function declaration \c f must have type <tt> range_1 .. range_n -> range</tt>.
       \c v must have sort range. The sort of the result is <tt>[domain_i -> range]</tt>.
       
       \sa Z3_mk_array_sort
       \sa Z3_mk_store
       \sa Z3_mk_select
    */
    Z3_ast Z3_API Z3_mk_map(__in Z3_context c, __in Z3_func_decl f, unsigned n, __in Z3_ast const* args);

    /** 
        \brief Access the array default value.
        Produces the default range value, for arrays that can be represented as 
        finite maps with a default range value.

        \param c logical context.
        \param array array value whose default range value is accessed.

    */
    Z3_ast Z3_API Z3_mk_array_default(__in Z3_context c, __in Z3_ast array);


    /*@}*/

    /**
       @name Sets
    */
    /*@{*/

    /**
       \brief Create Set type.
    */
    Z3_sort Z3_API Z3_mk_set_sort(__in Z3_context c, __in Z3_sort ty);

    /** 
        \brief Create the empty set.
    */
    Z3_ast Z3_API Z3_mk_empty_set(__in Z3_context c, __in Z3_sort domain);

    /** 
        \brief Create the full set.
    */
    Z3_ast Z3_API Z3_mk_full_set(__in Z3_context c, __in Z3_sort domain);

    /**
       \brief Add an element to a set.
       
       The first argument must be a set, the second an element.
    */
    Z3_ast Z3_API Z3_mk_set_add(__in Z3_context c, __in Z3_ast set, __in Z3_ast elem);

    /**
       \brief Remove an element to a set.
       
       The first argument must be a set, the second an element.
    */
    Z3_ast Z3_API Z3_mk_set_del(__in Z3_context c, __in Z3_ast set, __in Z3_ast elem);

    /**
       \brief Take the union of a list of sets.
    */
    Z3_ast Z3_API Z3_mk_set_union(__in Z3_context c, __in unsigned num_args, __in_ecount(num_args) Z3_ast const args[]);

    /**
       \brief Take the intersection of a list of sets.
    */
    Z3_ast Z3_API Z3_mk_set_intersect(__in Z3_context c, __in unsigned num_args, __in_ecount(num_args) Z3_ast const args[]);

    /**
       \brief Take the set difference between two sets.
    */
    Z3_ast Z3_API Z3_mk_set_difference(__in Z3_context c, __in Z3_ast arg1, __in Z3_ast arg2);

    /**
       \brief Take the complement of a set.
    */
    Z3_ast Z3_API Z3_mk_set_complement(__in Z3_context c, __in Z3_ast arg);


    /**
       \brief Check for set membership.
       
       The first argument should be an element type of the set.
    */
    Z3_ast Z3_API Z3_mk_set_member(__in Z3_context c, __in Z3_ast elem, __in Z3_ast set);

    /**
       \brief Check for subsetness of sets.
    */
    Z3_ast Z3_API Z3_mk_set_subset(__in Z3_context c, __in Z3_ast arg1, __in Z3_ast arg2);
    /*@}*/

    /**
       @name Numerals
    */
    /*@{*/

    /**
       \brief Create a numeral of a given sort. 

       \param c logical context.
       \param numeral A string representing the numeral value in decimal notation. If the given sort is a real, then the numeral can be a rational, that is, a string of the form <tt>[num]* / [num]*</tt>.
       \param ty The sort of the numeral. In the current implementation, the given sort can be an int, real, or bit-vectors of arbitrary size. 
       
       \sa Z3_mk_int
       \sa Z3_mk_unsigned_int
    */
    Z3_ast Z3_API Z3_mk_numeral(__in Z3_context c, __in_z Z3_string numeral, __in Z3_sort ty);

    /**
       \brief Create a real from a fraction.

       \param c logical context.
       \param num numerator of rational.
       \param den denomerator of rational.

       \pre den != 0

       \sa Z3_mk_numeral
       \sa Z3_mk_int
       \sa Z3_mk_unsigned_int
    */
    Z3_ast Z3_API Z3_mk_real(__in Z3_context c, __in_z int num, __in_z int den);
    
    /**
       \brief Create a numeral of a given sort. 
       
       This function can be use to create numerals that fit in a machine integer.
       It is slightly faster than #Z3_mk_numeral since it is not necessary to parse a string.

       \sa Z3_mk_numeral
    */
    Z3_ast Z3_API Z3_mk_int(__in Z3_context c, __in int v, __in Z3_sort ty);
    
    /**
       \brief Create a numeral of a given sort. 
       
       This function can be use to create numerals that fit in a machine unsinged integer.
       It is slightly faster than #Z3_mk_numeral since it is not necessary to parse a string.

       \sa Z3_mk_numeral
    */
    Z3_ast Z3_API Z3_mk_unsigned_int(__in Z3_context c, __in unsigned v, __in Z3_sort ty);

#ifndef CAMLIDL
    /**
       \brief Create a numeral of a given sort. 
       
       This function can be use to create numerals that fit in a machine __int64 integer.
       It is slightly faster than #Z3_mk_numeral since it is not necessary to parse a string.

       \sa Z3_mk_numeral
    */
    Z3_ast Z3_API Z3_mk_int64(__in Z3_context c, __in __int64 v, __in Z3_sort ty);
#endif // CAMLIDL

#ifndef CAMLIDL
    /**
       \brief Create a numeral of a given sort. 
       
       This function can be use to create numerals that fit in a machine unsigned __int64 integer.
       It is slightly faster than #Z3_mk_numeral since it is not necessary to parse a string.

       \sa Z3_mk_numeral
    */
    Z3_ast Z3_API Z3_mk_unsigned_int64(__in Z3_context c, __in unsigned __int64 v, __in Z3_sort ty);
#endif // CAMLIDL

    /*@}*/

    /**
       @name Quantifiers
    */
    /*@{*/

    /**
       \brief Create a pattern for quantifier instantiation.

       Z3 uses pattern matching to instantiate quantifiers. If a
       pattern is not provided for a quantifier, then Z3 will
       automatically compute a set of patterns for it. However, for
       optimal performance, the user should provide the patterns.

       Patterns comprise a list of terms. The list should be
       non-empty.  If the list comprises of more than one term, it is
       a called a multi-pattern.
       
       In general, one can pass in a list of (multi-)patterns in the
       quantifier constructor.


       \sa Z3_mk_forall
       \sa Z3_mk_exists
    */
    Z3_pattern Z3_API Z3_mk_pattern(
        __in Z3_context c,
        __in unsigned num_patterns, __in_ecount(num_patterns) Z3_ast const terms[]);

    /**
       \brief Create a bound variable.

       Bound variables are indexed by de-Bruijn indices. It is perhaps easiest to explain
       the meaning of de-Bruijn indices by indicating the compilation process from
       non-de-Bruijn formulas to de-Bruijn format.

       \verbatim 
       abs(forall (x1) phi) = forall (x1) abs1(phi, x1, 0)
       abs(forall (x1, x2) phi) = abs(forall (x1) abs(forall (x2) phi))
       abs1(x, x, n) = b_n
       abs1(y, x, n) = y
       abs1(f(t1,...,tn), x, n) = f(abs1(t1,x,n), ..., abs1(tn,x,n))
       abs1(forall (x1) phi, x, n) = forall (x1) (abs1(phi, x, n+1))
       \endverbatim

       The last line is significant: the index of a bound variable is different depending
       on the scope in which it appears. The deeper x appears, the higher is its
       index.
       
       \param c logical context
       \param index de-Bruijn index
       \param ty sort of the bound variable

       \sa Z3_mk_forall
       \sa Z3_mk_exists
    */
    Z3_ast Z3_API Z3_mk_bound(__in Z3_context c, __in unsigned index, __in Z3_sort ty);
    
    /**
       \brief Create a forall formula.

       \mlonly [mk_forall c w p t n b] creates a forall formula, where
       [w] is the weight, [p] is an array of patterns, [t] is an array
       with the sorts of the bound variables, [n] is an array with the
       'names' of the bound variables, and [b] is the body of the
       quantifier. Quantifiers are associated with weights indicating
       the importance of using the quantifier during
       instantiation. \endmlonly
       
       \param c logical context.
       \param weight quantifiers are associated with weights indicating the importance of using the quantifier during instantiation. By default, pass the weight 0.
       \param num_patterns number of patterns.
       \param patterns array containing the patterns created using #Z3_mk_pattern.
       \param num_decls number of variables to be bound.
       \param sorts the sorts of the bound variables.
       \param decl_names names of the bound variables
       \param body the body of the quantifier.
       
       \sa Z3_mk_pattern
       \sa Z3_mk_bound
       \sa Z3_mk_exists
    */
    Z3_ast Z3_API Z3_mk_forall(__in Z3_context c, __in unsigned weight,
                               __in unsigned num_patterns, __in_ecount(num_patterns) Z3_pattern const patterns[],
                               __in unsigned num_decls, __in_ecount(num_decls) Z3_sort const sorts[],
                               __in_ecount(num_decls) Z3_symbol const decl_names[],
                               __in Z3_ast body);

    /**
       \brief Create an exists formula. Similar to #Z3_mk_forall.
       
       \sa Z3_mk_pattern
       \sa Z3_mk_bound
       \sa Z3_mk_forall
    */
    Z3_ast Z3_API Z3_mk_exists(__in Z3_context c, __in unsigned weight,
                               __in unsigned num_patterns, __in_ecount(num_patterns) Z3_pattern const patterns[],
                               __in unsigned num_decls, __in_ecount(num_decls) Z3_sort const sorts[],
                               __in_ecount(num_decls) Z3_symbol const decl_names[],
                               __in Z3_ast body);

    /**
       \brief Create a quantifier - universal or existential, with pattern hints.
       
       \param c logical context.
       \param is_forall flag to indicate if this is a universal or existential quantifier.
       \param weight quantifiers are associated with weights indicating the importance of using the quantifier during instantiation. By default, pass the weight 0.
       \param num_patterns number of patterns.
       \param patterns array containing the patterns created using #Z3_mk_pattern.
       \param num_decls number of variables to be bound.
       \param sorts array of sorts of the bound variables.
       \param decl_names names of the bound variables.
       \param body the body of the quantifier.
       
       \sa Z3_mk_pattern
       \sa Z3_mk_bound
       \sa Z3_mk_forall
       \sa Z3_mk_exists
    */

    Z3_ast Z3_API Z3_mk_quantifier(
        __in Z3_context c, 
        __in Z3_bool is_forall, 
        __in unsigned weight, 
        __in unsigned num_patterns, __in_ecount(num_patterns) Z3_pattern const* patterns, 
        __in unsigned num_decls, __in_ecount(num_decls) Z3_sort const* sorts, 
        __in_ecount(num_decls) Z3_symbol const* decl_names, 
        __in Z3_ast body);


    /**
       \brief Create a quantifier - universal or existential, with pattern hints, no patterns, and attributes
       
       \param c logical context.
       \param is_forall flag to indicate if this is a universal or existential quantifier.
       \param quantifier_id identifier to identify quantifier
       \param skolem_id identifier to identify skolem constants introduced by quantifier.
       \param weight quantifiers are associated with weights indicating the importance of using the quantifier during instantiation. By default, pass the weight 0.
       \param num_patterns number of patterns.
       \param patterns array containing the patterns created using #Z3_mk_pattern.
       \param num_no_patterns number of patterns.
       \param no_patterns array containing the patterns created using #Z3_mk_pattern.
       \param num_decls number of variables to be bound.
       \param sorts array of sorts of the bound variables.
       \param decl_names names of the bound variables.
       \param body the body of the quantifier.
       
       \sa Z3_mk_pattern
       \sa Z3_mk_bound
       \sa Z3_mk_forall
       \sa Z3_mk_exists
    */

    Z3_ast Z3_API Z3_mk_quantifier_ex(
        __in Z3_context c, 
        __in Z3_bool is_forall, 
        __in unsigned weight, 
        __in Z3_symbol quantifier_id,
        __in Z3_symbol skolem_id,
        __in unsigned num_patterns, __in_ecount(num_patterns) Z3_pattern const* patterns, 
        __in unsigned num_no_patterns, __in_ecount(num_no_patterns) Z3_ast const* no_patterns, 
        __in unsigned num_decls, __in_ecount(num_decls) Z3_sort const* sorts, 
        __in_ecount(num_decls) Z3_symbol const* decl_names, 
        __in Z3_ast body);

    /**
       \brief Create a universal quantifier using a list of constants that
       will form the set of bound variables.

       \param c logical context.
       \param weight quantifiers are associated with weights indicating the importance of using 
              the quantifier during instantiation. By default, pass the weight 0.
       \param num_bound number of constants to be abstracted into bound variables.
       \param bound array of constants to be abstracted into bound variables.
       \param num_patterns number of patterns.
       \param patterns array containing the patterns created using #Z3_mk_pattern.
       \param body the body of the quantifier.
       
       \sa Z3_mk_pattern
       \sa Z3_mk_exists_const

    */

    Z3_ast Z3_API Z3_mk_forall_const(
        __in Z3_context c, 
        unsigned weight,
        unsigned num_bound,
        __in_ecount(num_bound) Z3_app const* bound,
        unsigned num_patterns,
        __in_ecount(num_patterns) Z3_pattern const* patterns,
        __in Z3_ast body
        );

    /**
       \brief Similar to #Z3_mk_forall_const.

       \brief Create an existential quantifier using a list of constants that
       will form the set of bound variables.

       \param c logical context.
       \param weight quantifiers are associated with weights indicating the importance of using 
              the quantifier during instantiation. By default, pass the weight 0.
       \param num_bound number of constants to be abstracted into bound variables.
       \param bound array of constants to be abstracted into bound variables.
       \param num_patterns number of patterns.
       \param patterns array containing the patterns created using #Z3_mk_pattern.
       \param body the body of the quantifier.
       
       \sa Z3_mk_pattern
       \sa Z3_mk_forall_const
    */

    Z3_ast Z3_API Z3_mk_exists_const(
        __in Z3_context c, 
        unsigned weight,
        unsigned num_bound,
        __in_ecount(num_bound) Z3_app const* bound,
        unsigned num_patterns,
        __in_ecount(num_patterns) Z3_pattern const* patterns,
        __in Z3_ast body
        );

    /**
       \brief Create a universal or existential 
       quantifier using a list of constants that
       will form the set of bound variables.
    */

    Z3_ast Z3_API Z3_mk_quantifier_const(
        __in Z3_context c, 
        Z3_bool is_forall,
        unsigned weight,
        unsigned num_bound,  __in_ecount(num_bound) Z3_app const* bound,
        unsigned num_patterns, __in_ecount(num_patterns) Z3_pattern const* patterns,
        __in Z3_ast body
        );



    /**
       \brief Create a universal or existential 
       quantifier using a list of constants that
       will form the set of bound variables.
    */

    Z3_ast Z3_API Z3_mk_quantifier_const_ex(
        __in Z3_context c, 
        Z3_bool is_forall,
        unsigned weight,
        __in Z3_symbol quantifier_id,
        __in Z3_symbol skolem_id,
        unsigned num_bound,  __in_ecount(num_bound) Z3_app const* bound,
        unsigned num_patterns, __in_ecount(num_patterns) Z3_pattern const* patterns,
        unsigned num_no_patterns, __in_ecount(num_no_patterns) Z3_ast const* no_patterns,
        __in Z3_ast body
        );




    /*@}*/


    /**
       @name Accessors
    */
    /*@{*/

    /** 
        \brief Return a unique identifier for \c t.
    */
    unsigned Z3_API Z3_get_ast_id(__in Z3_context c, Z3_ast t);

    /** 
        \brief Return a unique identifier for \c f.
    */
    unsigned Z3_API Z3_get_func_decl_id(__in Z3_context c, Z3_func_decl f);

    /** 
        \brief Return a unique identifier for \c s.
    */
    unsigned Z3_API Z3_get_sort_id(__in Z3_context c, Z3_sort s);



    /**
       \brief Return true if the given expression \c t is well sorted.
    */
    Z3_bool Z3_API Z3_is_well_sorted(__in Z3_context c, __in Z3_ast t);

    /**
       \brief Return \c Z3_INT_SYMBOL if the symbol was constructed
       using #Z3_mk_int_symbol, and \c Z3_STRING_SYMBOL if the symbol
       was constructed using #Z3_mk_string_symbol.
    */
    Z3_symbol_kind Z3_API Z3_get_symbol_kind(__in Z3_context c, __in Z3_symbol s);

    /**
       \brief \mlh get_symbol_int c s \endmlh
       Return the symbol int value. 
       
       \pre Z3_get_symbol_kind(s) == Z3_INT_SYMBOL

       \sa Z3_mk_int_symbol
    */
    int Z3_API Z3_get_symbol_int(__in Z3_context c, __in Z3_symbol s);
    
    /**
       \brief \mlh get_symbol_string c s \endmlh
       Return the symbol name. 

       \pre Z3_get_symbol_string(s) == Z3_STRING_SYMBOL

       \conly \warning The returned buffer is statically allocated by Z3. It will
       \conly be automatically deallocated when #Z3_del_context is invoked.
       \conly So, the buffer is invalidated in the next call to \c Z3_get_symbol_string.

       \sa Z3_mk_string_symbol
    */
    Z3_string Z3_API Z3_get_symbol_string(__in Z3_context c, __in Z3_symbol s);


    /**
       \brief Return the kind of the given AST.
    */
    Z3_ast_kind Z3_API Z3_get_ast_kind(__in Z3_context c, __in Z3_ast a);

    
    /**
       \brief Return numeral value, as a string of a numeric constant term

       \pre Z3_get_ast_kind(c, a) == Z3_NUMERAL_AST
    */
    Z3_string Z3_API Z3_get_numeral_string(__in Z3_context c, __in Z3_ast a);


    /**
       \brief Return numeral value, as a pair of 64 bit numbers if the representation fits.

       \param c logical context.
       \param a term.
       \param num numerator.
       \param den denominator.
       
       Preturn \c Z3_TRUE if the numeral value fits in 64 bit numerals, \c Z3_FALSE otherwise.

       \pre Z3_get_ast_kind(a) == Z3_NUMERAL_AST
    */
    Z3_bool Z3_API Z3_get_numeral_small(__in Z3_context c, __in Z3_ast a, __out __int64* num, __out __int64* den);


    /**
       \brief \mlh get_numeral_int c v \endmlh
       Similar to #Z3_get_numeral_string, but only succeeds if
       the value can fit in a machine int. Return Z3_TRUE if the call succeeded.

       \pre Z3_get_ast_kind(c, v) == Z3_NUMERAL_AST
      
       \sa Z3_get_numeral_string
    */
    Z3_bool Z3_API Z3_get_numeral_int(__in Z3_context c, __in Z3_ast v, __out int* i);

    /**
       \brief \mlh get_numeral_uint c v \endmlh
       Similar to #Z3_get_numeral_string, but only succeeds if
       the value can fit in a machine unsigned int. Return Z3_TRUE if the call succeeded.

       \pre Z3_get_ast_kind(c, v) == Z3_NUMERAL_AST
      
       \sa Z3_get_numeral_string
    */
    Z3_bool Z3_API Z3_get_numeral_uint(__in Z3_context c, __in Z3_ast v, __out unsigned* u);

#ifndef CAMLIDL
    /**
       \brief \mlh get_numeral_uint64 c v \endmlh
       Similar to #Z3_get_numeral_string, but only succeeds if
       the value can fit in a machine unsigned __int64 int. Return Z3_TRUE if the call succeeded.

       \pre Z3_get_ast_kind(c, v) == Z3_NUMERAL_AST
      
       \sa Z3_get_numeral_string
    */
    Z3_bool Z3_API Z3_get_numeral_uint64(__in Z3_context c, __in Z3_ast v, __out unsigned __int64* u);
#endif // CAMLIDL

#ifndef CAMLIDL
    /**
       \brief \mlh get_numeral_int64 c v \endmlh
       Similar to #Z3_get_numeral_string, but only succeeds if
       the value can fit in a machine __int64 int. Return Z3_TRUE if the call succeeded.

       \pre Z3_get_ast_kind(c, v) == Z3_NUMERAL_AST

       \sa Z3_get_numeral_string
    */
    Z3_bool Z3_API Z3_get_numeral_int64(__in Z3_context c, __in Z3_ast v, __out __int64* i);
#endif // CAMLIDL

#ifndef CAMLIDL
    /**
       \brief \mlh get_numeral_rational_int64 c x y\endmlh
       Similar to #Z3_get_numeral_string, but only succeeds if
       the value can fit as a reational number as machine __int64 int. Return Z3_TRUE if the call succeeded.

       \pre Z3_get_ast_kind(c, v) == Z3_NUMERAL_AST

       \sa Z3_get_numeral_string
    */
    Z3_bool Z3_API Z3_get_numeral_rational_int64(__in Z3_context c, __in Z3_ast v, __out __int64* num, __out __int64* den);
#endif // CAMLIDL

    /**
       \brief Return Z3_L_TRUE if \c a is true, Z3_L_FALSE if it is false, and Z3_L_UNDEF otherwise.
    */
    Z3_lbool Z3_API Z3_get_bool_value(__in Z3_context c, __in Z3_ast a);

    /**
       \brief Return the declaration of a constant or function application.
    */
    Z3_func_decl Z3_API Z3_get_app_decl(__in Z3_context c, __in Z3_app a);

    /**
       \brief \mlh get_app_num_args c a \endmlh
       Return the number of argument of an application. If \c t
       is an constant, then the number of arguments is 0.
    */
    unsigned Z3_API Z3_get_app_num_args(__in Z3_context c, __in Z3_app a);

    /**
       \brief \mlh get_app_arg c a i \endmlh
       Return the i-th argument of the given application.
       
       \pre i < Z3_get_num_args(c, a)
    */
    Z3_ast Z3_API Z3_get_app_arg(__in Z3_context c, __in Z3_app a, __in unsigned i);

    /**
       \brief Return index of de-Brujin bound variable.

       \pre Z3_get_ast_kind(a) == Z3_VAR_AST
    */
    unsigned Z3_API Z3_get_index_value(__in Z3_context c, __in Z3_ast a);

    /**
       \brief Determine if quantifier is universal.
       
       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST
    */
    Z3_bool Z3_API Z3_is_quantifier_forall(__in Z3_context c, __in Z3_ast a);

    /**
       \brief Obtain weight of quantifier.
       
       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST
    */
    unsigned Z3_API Z3_get_quantifier_weight(__in Z3_context c, __in Z3_ast a);

    /**
       \brief Return number of patterns used in quantifier.
       
       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST
    */
    unsigned Z3_API Z3_get_quantifier_num_patterns(__in Z3_context c, __in Z3_ast a);

    /**
       \brief Return i'th pattern.
       
       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST
    */
    Z3_pattern Z3_API Z3_get_quantifier_pattern_ast(__in Z3_context c, __in Z3_ast a, unsigned i);

    /**
       \brief Return number of no_patterns used in quantifier.
       
       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST
    */
    unsigned Z3_API Z3_get_quantifier_num_no_patterns(__in Z3_context c, __in Z3_ast a);

    /**
       \brief Return i'th no_pattern.
       
       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST
    */
    Z3_ast Z3_API Z3_get_quantifier_no_pattern_ast(__in Z3_context c, __in Z3_ast a, unsigned i);

    /**
       \brief Return symbol of the i'th bound variable.
       
       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST
    */
    Z3_symbol Z3_API Z3_get_quantifier_bound_name(__in Z3_context c, __in Z3_ast a, unsigned i);

    /**
       \brief Return sort of the i'th bound variable.
       
       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST
    */
    Z3_sort Z3_API Z3_get_quantifier_bound_sort(__in Z3_context c, __in Z3_ast a, unsigned i);

    /**
       \brief Return body of quantifier.
       
       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST
    */
    Z3_ast Z3_API Z3_get_quantifier_body(__in Z3_context c, __in Z3_ast a);



    /**
       \brief Return number of bound variables of quantifier.
       
       \pre Z3_get_ast_kind(a) == Z3_QUANTIFIER_AST
    */
    unsigned Z3_API Z3_get_quantifier_num_bound(__in Z3_context c, __in Z3_ast a);

    /**
       \brief Return the constant declaration name as a symbol. 
    */
    Z3_symbol Z3_API Z3_get_decl_name(__in Z3_context c, __in Z3_func_decl d);

    /**
       \brief Return the number of parameters associated with a declaration.
    */
    unsigned Z3_API Z3_get_decl_num_parameters(__in Z3_context c, __in Z3_func_decl d);

    /**
       \brief Return the parameter type associated with a declaration.
       
       \param c the context
       \param d the function declaration
       \param idx is the index of the named parameter it should be between 0 and the number of parameters.
    */
    Z3_parameter_kind Z3_API Z3_get_decl_parameter_kind(__in Z3_context c, __in Z3_func_decl d, unsigned idx);

    /**
       \brief Return the integer value associated with an integer parameter.

       \pre Z3_get_decl_parameter_kind(c, d, idx) == Z3_PARAMETER_INT
    */
    int Z3_API Z3_get_decl_int_parameter(__in Z3_context c, __in Z3_func_decl d, unsigned idx);

    /**
       \brief Return the double value associated with an double parameter.

       \pre Z3_get_decl_parameter_kind(c, d, idx) == Z3_PARAMETER_DOUBLE
    */
    double Z3_API Z3_get_decl_double_parameter(__in Z3_context c, __in Z3_func_decl d, unsigned idx);

    /**
       \brief Return the double value associated with an double parameter.

       \pre Z3_get_decl_parameter_kind(c, d, idx) == Z3_PARAMETER_SYMBOL
    */
    Z3_symbol Z3_API Z3_get_decl_symbol_parameter(__in Z3_context c, __in Z3_func_decl d, unsigned idx);
    /**
       \brief Return the sort value associated with a sort parameter.

       \pre Z3_get_decl_parameter_kind(c, d, idx) == Z3_PARAMETER_SORT
    */
    Z3_sort Z3_API Z3_get_decl_sort_parameter(__in Z3_context c, __in Z3_func_decl d, unsigned idx);

    /**
       \brief Return the expresson value associated with an expression parameter.

       \pre Z3_get_decl_parameter_kind(c, d, idx) == Z3_PARAMETER_AST
    */
    Z3_ast Z3_API Z3_get_decl_ast_parameter(__in Z3_context c, __in Z3_func_decl d, unsigned idx);

    /**
       \brief Return the expresson value associated with an expression parameter.

       \pre Z3_get_decl_parameter_kind(c, d, idx) == Z3_PARAMETER_FUNC_DECL
    */
    Z3_func_decl Z3_API Z3_get_decl_func_decl_parameter(__in Z3_context c, __in Z3_func_decl d, unsigned idx);

    /**
       \brief Return the rational value, as a string, associated with a rational parameter.

       \pre Z3_get_decl_parameter_kind(c, d, idx) == Z3_PARAMETER_RATIONAL
    */
    Z3_string Z3_API Z3_get_decl_rational_parameter(__in Z3_context c, __in Z3_func_decl d, unsigned idx);

    /**
       \brief Return the sort name as a symbol. 
    */
    Z3_symbol Z3_API Z3_get_sort_name(__in Z3_context c, __in Z3_sort d);

    /**
       \brief Return the sort of an AST node.
       
       The AST node must be a constant, application, numeral, bound variable, or quantifier.

    */
    Z3_sort Z3_API Z3_get_sort(__in Z3_context c, __in Z3_ast a);

    /**
       \brief Return the number of parameters of the given declaration.

       \sa Z3_get_domain_size
    */
    unsigned Z3_API Z3_get_domain_size(__in Z3_context c, __in Z3_func_decl d);

    /**
       \brief \mlh get_domain c d i \endmlh
       Return the sort of the i-th parameter of the given function declaration.
       
       \pre i < Z3_get_domain_size(d)

       \sa Z3_get_domain_size
    */
    Z3_sort Z3_API Z3_get_domain(__in Z3_context c, __in Z3_func_decl d, __in unsigned i);

    /**
       \brief \mlh get_range c d \endmlh
       Return the range of the given declaration. 

       If \c d is a constant (i.e., has zero arguments), then this
       function returns the sort of the constant.
    */
    Z3_sort Z3_API Z3_get_range(__in Z3_context c, __in Z3_func_decl d);

    /**
       \brief Return the sort kind (e.g., array, tuple, int, bool, etc).

       \sa Z3_sort_kind
    */
    Z3_sort_kind Z3_API Z3_get_sort_kind(__in Z3_context c, __in Z3_sort t);

    /**
       \brief \mlh get_bv_sort_size c t \endmlh
       Return the size of the given bit-vector sort. 

       \pre Z3_get_sort_kind(c, t) == Z3_BV_SORT

       \sa Z3_mk_bv_sort
       \sa Z3_get_sort_kind
    */
    unsigned Z3_API Z3_get_bv_sort_size(__in Z3_context c, __in Z3_sort t);

    /**
       \brief \mlh get_array_sort_domain c t \endmlh
       Return the domain of the given array sort.
       
       \pre Z3_get_sort_kind(c, t) == Z3_ARRAY_SORT

       \sa Z3_mk_array_sort
       \sa Z3_get_sort_kind
    */
    Z3_sort Z3_API Z3_get_array_sort_domain(__in Z3_context c, __in Z3_sort t);

    /**
       \brief \mlh get_array_sort_range c t \endmlh 
       Return the range of the given array sort. 

       \pre Z3_get_sort_kind(c, t) == Z3_ARRAY_SORT

       \sa Z3_mk_array_sort
       \sa Z3_get_sort_kind
    */
    Z3_sort Z3_API Z3_get_array_sort_range(__in Z3_context c, __in Z3_sort t);

    /**
       \brief \mlh get_tuple_sort_mk_decl c t \endmlh
       Return the constructor declaration of the given tuple
       sort. 

       \pre Z3_get_sort_kind(c, t) == Z3_DATATYPE_SORT

       \sa Z3_mk_tuple_sort
       \sa Z3_get_sort_kind
    */
    Z3_func_decl Z3_API Z3_get_tuple_sort_mk_decl(__in Z3_context c, __in Z3_sort t);

    /**
       \brief Return declaration kind corresponding to declaration.
    */
    Z3_decl_kind Z3_API Z3_get_decl_kind(__in Z3_context c, __in Z3_func_decl d);
    
    /**
       \brief \mlh get_tuple_sort_num_fields c t \endmlh
       Return the number of fields of the given tuple sort. 

       \pre Z3_get_sort_kind(c, t) == Z3_DATATYPE_SORT

       \mlonly \remark Consider using the function {!Z3.get_tuple_sort}, which 
       returns a tuple: tuple constructor, and an array of the tuple sort fields. \endmlonly

       \sa Z3_mk_tuple_sort
       \sa Z3_get_sort_kind
    */
    unsigned Z3_API Z3_get_tuple_sort_num_fields(__in Z3_context c, __in Z3_sort t);

    /**
       \brief \mlh get_tuple_sort_field_decl c t i \endmlh
       Return the i-th field declaration (i.e., projection function declaration)
       of the given tuple sort. 

       \mlonly \remark Consider using the function {!Z3.get_tuple_sort}, which 
       returns a tuple: tuple constructor, and an array of the tuple sort fields. \endmlonly

       \pre Z3_get_sort_kind(t) == Z3_DATATYPE_SORT
       \pre i < Z3_get_tuple_sort_num_fields(c, t)
       
       \sa Z3_mk_tuple_sort
       \sa Z3_get_sort_kind
    */
    Z3_func_decl Z3_API Z3_get_tuple_sort_field_decl(__in Z3_context c, __in Z3_sort t, __in unsigned i);

    /** 
        \brief Return number of constructors for datatype.

        \pre Z3_get_sort_kind(t) == Z3_DATATYPE_SORT

        \sa Z3_get_datatype_sort_constructor
        \sa Z3_get_datatype_sort_recognizer
        \sa Z3_get_datatype_sort_constructor_accessor

    */
    unsigned Z3_API Z3_get_datatype_sort_num_constructors(
        __in Z3_context c, __in Z3_sort t);

    /** 
        \brief Return idx'th constructor.

        \pre Z3_get_sort_kind(t) == Z3_DATATYPE_SORT
        \pre idx < Z3_get_datatype_sort_num_constructors(c, t)

        \sa Z3_get_datatype_sort_num_constructors
        \sa Z3_get_datatype_sort_recognizer
        \sa Z3_get_datatype_sort_constructor_accessor

    */
    Z3_func_decl Z3_API Z3_get_datatype_sort_constructor(
        __in Z3_context c, __in Z3_sort t, unsigned idx);

    /** 
        \brief Return idx'th recognizer.

        \pre Z3_get_sort_kind(t) == Z3_DATATYPE_SORT
        \pre idx < Z3_get_datatype_sort_num_constructors(c, t)

        \sa Z3_get_datatype_sort_num_constructors
        \sa Z3_get_datatype_sort_constructor
        \sa Z3_get_datatype_sort_constructor_accessor

    */
    Z3_func_decl Z3_API Z3_get_datatype_sort_recognizer(
        __in Z3_context c, __in Z3_sort t, unsigned idx);

    /** 
        \brief Return idx_a'th accessor for the idx_c'th constructor.

        \pre Z3_get_sort_kind(t) == Z3_DATATYPE_SORT
        \pre idx_c < Z3_get_datatype_sort_num_constructors(c, t)
        \pre idx_a < Z3_get_domain_size(c, Z3_get_datatype_sort_constructor(c, idx_c))

        \sa Z3_get_datatype_sort_num_constructors
        \sa Z3_get_datatype_sort_constructor
        \sa Z3_get_datatype_sort_recognizer
    */
    Z3_func_decl Z3_API Z3_get_datatype_sort_constructor_accessor(
        __in Z3_context c, __in Z3_sort t, unsigned idx_c, unsigned idx_a);


    /** 
        \brief Return arity of relation.

        \pre Z3_get_sort_kind(s) == Z3_RELATION_SORT

        \sa Z3_get_relation_column
    */

    unsigned Z3_API Z3_get_relation_arity(__in Z3_context c, __in Z3_sort s);

    /** 
        \brief Return sort at i'th column of relation sort.

        \pre Z3_get_sort_kind(c, s) == Z3_RELATION_SORT
        \pre col < Z3_get_relation_arity(c, s)

        \sa Z3_get_relation_arity
    */
    Z3_sort Z3_API Z3_get_relation_column(__in Z3_context c, __in Z3_sort s, unsigned col);


#ifndef CAMLIDL
    /** 
        \brief Store the size of the sort in \c r. Return Z3_TRUE if the call succeeded.
        That is, Z3_get_sort_kind(s) == Z3_FINITE_DOMAIN_SORT
    */
    Z3_bool Z3_API Z3_get_finite_domain_sort_size(__in Z3_context c, __in Z3_sort s, __out unsigned __int64* r);
#endif

    /** 
        \brief Return number of terms in pattern.
    */
    unsigned Z3_API Z3_get_pattern_num_terms(__in Z3_context c, __in Z3_pattern p);
    
    /**
       \brief Return i'th ast in pattern.
    */
    Z3_ast Z3_API Z3_get_pattern(__in Z3_context c, __in Z3_pattern p, __in unsigned idx);



    /** 
        \brief Interface to simplifier.

        Provides an interface to the AST simplifier used by Z3.
        It allows clients to piggyback on top of the AST simplifier
        for their own term manipulation.
    */
    Z3_ast Z3_API Z3_simplify(__in Z3_context c, __in Z3_ast a);

    /*@}*/

    /**
       @name Modifiers
    */
    /*@{*/

    /**
       \brief Update the arguments of term \c a using the arguments \c args.
       The number of arguments \c num_args should coincide 
       with the number of arguments to \c a.
       If \c a is a quantifier, then num_args has to be 1.
    */
    Z3_ast Z3_API Z3_update_term(__in Z3_context c, __in Z3_ast a, __in unsigned num_args, __in_ecount(num_args) Z3_ast args[]);

    /**
       \brief Substitute every occurrence of <tt>from[i]</tt> in \c a with <tt>to[i]</tt>, for \c i smaller than \c num_exprs.
       The result is the new AST. The arrays \c from and \c to must have size \c num_exprs.
       For every \c i smaller than \c num_exprs, we must have that sort of <tt>from[i]</tt> must be equal to sort of <tt>to[i]</tt>.
    */
    Z3_ast Z3_API Z3_substitute(__in Z3_context c, 
                                __in Z3_ast a, 
                                __in unsigned num_exprs, 
                                __in_ecount(num_exprs) Z3_ast from[], 
                                __in_ecount(num_exprs) Z3_ast to[]);

    /**
       \brief Substitute the free variables in \c a with the expressions in \c to.
       For every \c i smaller than \c num_exprs, the variable with de-Bruijn index \c i is replaced with term <tt>to[i]</tt>.
    */
    Z3_ast Z3_API Z3_substitute_vars(__in Z3_context c, 
                                     __in Z3_ast a, 
                                     __in unsigned num_exprs, 
                                     __in_ecount(num_exprs) Z3_ast to[]);
    
    /*@}*/

    

    /**
       @name Coercions
    */
    /*@{*/

    /**
       \brief Convert a Z3_sort into Z3_ast. This is just type casting.
    */
    Z3_ast Z3_API Z3_sort_to_ast(__in Z3_context c, __in Z3_sort s);
    
    /**
       \brief Convert a Z3_func_decl into Z3_ast. This is just type casting.
    */
    Z3_ast Z3_API Z3_func_decl_to_ast(__in Z3_context c, __in Z3_func_decl f);
    
    /**
       \brief Convert a Z3_pattern into Z3_ast. This is just type casting.
    */
    Z3_ast Z3_API Z3_pattern_to_ast(__in Z3_context c, __in Z3_pattern p);

    /**
       \brief Convert a APP_AST into an AST. This is just type casting.
    */
    Z3_ast Z3_API Z3_app_to_ast(__in Z3_context c, __in Z3_app a);

    /**
       \brief Convert an AST into a APP_AST. This is just type casting.
       
       \warning This conversion is only safe if #Z3_get_ast_kind returns \c Z3_app.
    */
    Z3_app Z3_API Z3_to_app(__in Z3_context c, __in Z3_ast a);

    /*@}*/
    
    /**
       @name Constraints
    */
    /*@{*/

    /** 
        \brief Create a backtracking point.
        
        The logical context can be viewed as a stack of contexts.  The
        scope level is the number of elements on this stack. The stack
        of contexts is simulated using trail (undo) stacks.

        \sa Z3_pop
    */
    void Z3_API Z3_push(__in Z3_context c);
    
    /**
       \brief Backtrack.
       
       Restores the context from the top of the stack, and pops it off the
       stack.  Any changes to the logical context (by #Z3_assert_cnstr or
       other functions) between the matching #Z3_push and \c Z3_pop
       operators are flushed, and the context is completely restored to
       what it was right before the #Z3_push.
       
       \sa Z3_push
    */
    void Z3_API Z3_pop(__in Z3_context c, __in unsigned num_scopes);


    /**
       \brief Retrieve the current scope level.
       
       It retrieves the number of scopes that have been pushed, but not yet popped.
       
       \sa Z3_push
       \sa Z3_pop
    */
    unsigned Z3_API Z3_get_num_scopes(__in Z3_context c);
    
    /**
       \brief Persist AST through num_scopes pops.
       This function is only relevant if \c c was created using #Z3_mk_context.
       If \c c was created using #Z3_mk_context_rc, this function is a NOOP.
       
       Normally, for contexts created using #Z3_mk_context, 
       references to terms are no longer valid when 
       popping scopes beyond the level where the terms are created.
       If you want to reference a term below the scope where it
       was created, use this method to specify how many pops
       the term should survive.
       The num_scopes should be at most equal to the number of
       calls to Z3_push subtracted with the calls to Z3_pop.
    */
    void Z3_API Z3_persist_ast(__in Z3_context c, __in Z3_ast a, __in unsigned num_scopes);


    /**
       \brief Assert a constraing into the logical context.
       
       After one assertion, the logical context may become
       inconsistent.  
       
       The functions #Z3_check or #Z3_check_and_get_model should be
       used to check whether the logical context is consistent or not.

       \sa Z3_check
       \sa Z3_check_and_get_model
    */
    void Z3_API Z3_assert_cnstr(__in Z3_context c, __in Z3_ast a);
    
    /**
       \brief Check whether the given logical context is consistent or not.

       If the logical context is not unsatisfiable (i.e., the return value is different from \c Z3_L_FALSE)
       and model construction is enabled (see #Z3_mk_config), then a model is stored in \c m. Otherwise,
       the value \c 0 is stored in \c m.
       The caller is responsible for deleting the model using the function #Z3_del_model.
       
       \remark Model construction must be enabled using configuration
       parameters (See, #Z3_mk_config).

       \sa Z3_check
       \sa Z3_del_model
    */
    Z3_lbool Z3_API Z3_check_and_get_model(__in Z3_context c, __out Z3_model * m);
    
    /**
       \brief Check whether the given logical context is consistent or not.

       The function #Z3_check_and_get_model should be used when models are needed.

       \sa Z3_check_and_get_model
    */
    Z3_lbool Z3_API Z3_check(__in Z3_context c);

    /**
       \brief Check whether the given logical context and optional assumptions is consistent or not.

       If the logical context is not unsatisfiable (i.e., the return value is different from \c Z3_L_FALSE),
       a non-0 model argument is passed in,
       and model construction is enabled (see #Z3_mk_config), then a model is stored in \c m. 
       Otherwise, \c m is left unchanged.
       The caller is responsible for deleting the model using the function #Z3_del_model.
       
       \remark If the model argument is non-0, then model construction must be enabled using configuration
       parameters (See, #Z3_mk_config).

       \param c logical context.
       \param num_assumptions number of auxiliary assumptions.
       \param assumptions array of auxiliary assumptions
       \param m optional pointer to a model.
       \param proof optional pointer to a proof term.
       \param core_size size of unsatisfiable core. 
       \param core pointer to an array receiveing unsatisfiable core. 
              The unsatisfiable core is a subset of the assumptions, so the array has the same size as the assumptions.
              The \c core array is not populated if \c core_size is set to 0.

       \pre assumptions comprises of propositional literals.
            In other words, you cannot use compound formulas for assumptions, 
            but should use propositional variables or negations of propositional variables.
              
       \sa Z3_check
       \sa Z3_del_model
    */
    Z3_lbool Z3_API Z3_check_assumptions(
        __in Z3_context c, 
        __in unsigned num_assumptions, __in_ecount(num_assumptions) Z3_ast assumptions[], 
        __out Z3_model * m, __out Z3_ast* proof, 
        __inout unsigned* core_size, __inout_ecount(num_assumptions) Z3_ast core[]
        );

    /**
       \brief Retrieve congruence class representatives for terms.

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
       The function return Z3_L_FALSE if the current assertions are not satisfiable.

       \sa Z3_check_and_get_model
       \sa Z3_check
    */

    Z3_lbool Z3_API Z3_get_implied_equalities(
        __in Z3_context c, 
        __in unsigned num_terms,
        __in_ecount(num_terms) Z3_ast terms[],
        __out_ecount(num_terms) unsigned class_ids[]
        );


    /**
       \brief Delete a model object.
       
       \sa Z3_check_and_get_model
    */
    void Z3_API Z3_del_model(__in Z3_context c, __in Z3_model m);

    /**
       @name Search control.
    */
    /*@{*/
    /**
       \brief Cancel an ongoing check.
       
       Notifies the current check to abort and return.
       This method should be called from a different thread
       than the one performing the check.
    */

    void Z3_API Z3_soft_check_cancel(__in Z3_context c);
    /*@}*/

    /*@{*/

    /**
       \brief Retrieve reason for search failure.
       
       If a call to #Z3_check or #Z3_check_and_get_model returns Z3_L_UNDEF, 
       use this facility to determine the more detailed cause of search failure.
    */
    Z3_search_failure Z3_API Z3_get_search_failure(__in Z3_context c);

    /*@}*/


    /**
       @name Labels.
    */
    /*@{*/
    /** 
        \brief Retrieve the set of labels that were relevant in
        the context of the current satisfied context.

        \sa Z3_del_literals
        \sa Z3_get_num_literals
        \sa Z3_get_label_symbol
        \sa Z3_get_literal
    */
    Z3_literals Z3_API Z3_get_relevant_labels(__in Z3_context c);

    /** 
        \brief Retrieve the set of literals that satisfy the current context.

        \sa Z3_del_literals
        \sa Z3_get_num_literals
        \sa Z3_get_label_symbol
        \sa Z3_get_literal
    */
    Z3_literals Z3_API Z3_get_relevant_literals(__in Z3_context c);

    /** 
        \brief Retrieve the set of literals that whose assignment were 
        guess, but not propagated during the search.

        \sa Z3_del_literals
        \sa Z3_get_num_literals
        \sa Z3_get_label_symbol
        \sa Z3_get_literal
    */
    Z3_literals Z3_API Z3_get_guessed_literals(__in Z3_context c);


    /**
       \brief Delete a labels context.
       
       \sa Z3_get_relevant_labels
    */
    void Z3_API Z3_del_literals(__in Z3_context c, __in Z3_literals lbls);

    /**
       \brief Retrieve the number of label symbols that were returned.
       
       \sa Z3_get_relevant_labels
    */
    unsigned Z3_API Z3_get_num_literals(__in Z3_context c, __in Z3_literals lbls);

    /**
       \brief Retrieve label symbol at idx.
    */
    Z3_symbol Z3_API Z3_get_label_symbol(__in Z3_context c, __in Z3_literals lbls, __in unsigned idx);

    /**
       \brief Retrieve literal expression at idx.
    */
    Z3_ast Z3_API Z3_get_literal(__in Z3_context c, __in Z3_literals lbls, __in unsigned idx);

    /**
       \brief Disable label.
       
       The disabled label is not going to be used when blocking the subsequent search.

       \sa Z3_block_literals
    */
    void Z3_API Z3_disable_literal(__in Z3_context c, __in Z3_literals lbls, __in unsigned idx);

    /**
       \brief Block subsequent checks using the remaining enabled labels.
    */
    void Z3_API Z3_block_literals(__in Z3_context c, __in Z3_literals lbls);

    /*@}*/



    /**
       @name Model navigation
     */
    /*@{*/
    
    /**
       \brief Return the number of constants assigned by the given model.
       
       \mlonly \remark Consider using {!Z3.get_model_constants}. \endmlonly

       \sa Z3_get_model_constant
    */
    unsigned Z3_API Z3_get_model_num_constants(__in Z3_context c, __in Z3_model m);

    /**
       \brief \mlh get_model_constant c m i \endmlh
       Return the i-th constant in the given model. 

       \mlonly \remark Consider using {!Z3.get_model_constants}. \endmlonly

       \pre i < Z3_get_model_num_constants(c, m)

       \sa Z3_eval
    */
    Z3_func_decl Z3_API Z3_get_model_constant(__in Z3_context c, __in Z3_model m, __in unsigned i);

    /**
       \brief Return the value of the given constant or function 
              in the given model.
       
    */
    Z3_bool Z3_API Z3_eval_func_decl(__in Z3_context c, __in Z3_model m, __in Z3_func_decl decl, __out Z3_ast* v);


    /**
       \brief \mlh is_array_value c v \endmlh
       Determine whether the term encodes an array value.       
       Return the number of entries mapping to non-default values of the array.
    */
    Z3_bool Z3_API Z3_is_array_value(__in Z3_context c, __in Z3_model m, __in Z3_ast v, __out unsigned* num_entries);


    /**
       \brief \mlh get_array_value c v \endmlh
       An array values is represented as a dictionary plus a
       default (else) value. This function returns the array graph.

       \pre Z3_TRUE == Z3_is_array_value(c, v, &num_entries)       
    */
    void Z3_API Z3_get_array_value(__in Z3_context c, 
                                   __in Z3_model m,
                                   __in Z3_ast v,
                                   __in unsigned num_entries,
                                   __inout_ecount(num_entries) Z3_ast indices[],
                                   __inout_ecount(num_entries) Z3_ast values[],
                                   __out Z3_ast* else_value
                                   );

        
    /**
       \brief Return the number of function interpretations in the given model.
       
       A function interpretation is represented as a finite map and an 'else' value.
       Each entry in the finite map represents the value of a function given a set of arguments.

       \mlonly \remark Consider using {!Z3.get_model_funcs}. \endmlonly
       
       \sa Z3_get_model_func_decl
       \sa Z3_get_model_func_else
       \sa Z3_get_model_func_num_entries
       \sa Z3_get_model_func_entry_num_args
       \sa Z3_get_model_func_entry_arg
     */
    unsigned Z3_API Z3_get_model_num_funcs(__in Z3_context c, __in Z3_model m);
    
    
    /**
       \brief \mlh get_model_func_decl c m i \endmlh
       Return the declaration of the i-th function in the given model.

       \mlonly \remark Consider using {!Z3.get_model_funcs}. \endmlonly

       \pre i < Z3_get_model_num_funcs(c, m)

       \sa Z3_get_model_num_funcs
    */
    Z3_func_decl Z3_API Z3_get_model_func_decl(__in Z3_context c, __in Z3_model m, __in unsigned i);

    /**
       \brief \mlh get_model_func_else c m i \endmlh
       Return the 'else' value of the i-th function interpretation in the given model.
 
       A function interpretation is represented as a finite map and an 'else' value.

       \mlonly \remark Consider using {!Z3.get_model_funcs}. \endmlonly
       
       \pre i < Z3_get_model_num_funcs(c, m)

       \sa Z3_get_model_num_funcs
       \sa Z3_get_model_func_num_entries
       \sa Z3_get_model_func_entry_num_args
       \sa Z3_get_model_func_entry_arg
    */
    Z3_ast Z3_API Z3_get_model_func_else(__in Z3_context c, __in Z3_model m, __in unsigned i);

    /**
       \brief \mlh get_model_func_num_entries c m i \endmlh
       Return the number of entries of the i-th function interpretation in the given model.
 
       A function interpretation is represented as a finite map and an 'else' value.

       \mlonly \remark Consider using {!Z3.get_model_funcs}. \endmlonly
       
       \pre i < Z3_get_model_num_funcs(c, m)

       \sa Z3_get_model_num_funcs
       \sa Z3_get_model_func_else
       \sa Z3_get_model_func_entry_num_args
       \sa Z3_get_model_func_entry_arg
    */
    unsigned Z3_API Z3_get_model_func_num_entries(__in Z3_context c, __in Z3_model m, __in unsigned i);

    
    /**
       \brief \mlh get_model_func_entry_num_args c m i j \endmlh
       Return the number of arguments of the j-th entry of the i-th function interpretation in the given
       model.

       A function interpretation is represented as a finite map and an 'else' value.
       This function returns the j-th entry of this map.
      
       An entry represents the value of a function given a set of arguments.
       \conly That is: it has the following format <tt>f(args[0],...,args[num_args - 1]) = val</tt>.

       \mlonly \remark Consider using {!Z3.get_model_funcs}. \endmlonly

       \pre i < Z3_get_model_num_funcs(c, m)
       \pre j < Z3_get_model_func_num_entries(c, m, i)

       \sa Z3_get_model_num_funcs
       \sa Z3_get_model_func_num_entries 
       \sa Z3_get_model_func_entry_arg
    */
    unsigned Z3_API Z3_get_model_func_entry_num_args(__in Z3_context c,
                                                     __in Z3_model m,
                                                     __in unsigned i,
                                                     __in unsigned j);
    
    /**
       \brief \mlh get_model_func_entry_arg c m i j k \endmlh
       Return the k-th argument of the j-th entry of the i-th function interpretation in the given
       model.

       A function interpretation is represented as a finite map and an 'else' value.
       This function returns the j-th entry of this map.
      
       An entry represents the value of a function given a set of arguments.
       \conly That is: it has the following format <tt>f(args[0],...,args[num_args - 1]) = val</tt>.

       \mlonly \remark Consider using {!Z3.get_model_funcs}. \endmlonly

       \pre i < Z3_get_model_num_funcs(c, m)
       \pre j < Z3_get_model_func_num_entries(c, m, i)
       \pre k < Z3_get_model_func_entry_num_args(c, m, i, j)

       \sa Z3_get_model_num_funcs
       \sa Z3_get_model_func_num_entries 
       \sa Z3_get_model_func_entry_num_args
    */
    Z3_ast Z3_API Z3_get_model_func_entry_arg(__in Z3_context c,
                                                __in Z3_model m,
                                                __in unsigned i,
                                                __in unsigned j,
                                                __in unsigned k);
    
    /**
       \brief \mlh get_model_func_entry_value c m i j \endmlh
       Return the return value of the j-th entry of the i-th function interpretation in the given
       model.

       A function interpretation is represented as a finite map and an 'else' value.
       This function returns the j-th entry of this map.
      
       An entry represents the value of a function given a set of arguments.
       \conly That is: it has the following format <tt>f(args[0],...,args[num_args - 1]) = val</tt>.

       \mlonly \remark Consider using {!Z3.get_model_funcs}. \endmlonly

       \pre i < Z3_get_model_num_funcs(c, m)
       \pre j < Z3_get_model_func_num_entries(c, m, i)

       \sa Z3_get_model_num_funcs
       \sa Z3_get_model_func_num_entries 
    */
    Z3_ast Z3_API Z3_get_model_func_entry_value(__in Z3_context c,
                                                  __in Z3_model m,
                                                  __in unsigned i,
                                                  __in unsigned j);
    
    /**
       \brief \mlh eval c m t \endmlh
       Evaluate the AST node \c t in the given model. 
       \conly Return \c Z3_TRUE if succeeded, and store the result in \c v.
       \mlonly Return a pair: Boolean and value. The Boolean is true if the term was successfully evaluated. \endmlonly

       The evaluation may fail for the following reasons:

       - \c t contains a quantifier.

       - the model \c m is partial, that is, it doesn't have a complete interpretation for uninterpreted functions. 
         That is, the option <tt>MODEL_PARTIAL=true</tt> was used.

       - \c t is type incorrect.
    */
    Z3_bool Z3_API Z3_eval(__in Z3_context c, __in Z3_model m, __in Z3_ast t, __out Z3_ast * v);

    /**
       \brief Evaluate declaration given values.

       Provides direct way to evaluate declarations
       without going over terms.
     */
    Z3_bool Z3_API Z3_eval_decl(__in Z3_context c, __in Z3_model m, 
                                __in Z3_func_decl d, 
                                __in unsigned num_args,
                                __in_ecount(num_args) Z3_ast args[],
                                __out Z3_ast* v);



    
    /*@}*/

    /**
       @name Interaction logging.
    */
    /*@{*/
    
    /**
       \brief Log interaction to a file.
    */
    Z3_bool Z3_API Z3_open_log(__in Z3_context c, __in_z Z3_string filename);

    /**
       \brief Append user-defined string to interaction log.
       
       The interaction log is opened using Z3_open_log.
       It contains the formulas that are checked using Z3.
       You can use this command to append comments, for instance.
    */
    void Z3_API Z3_append_log(__in Z3_context c, __in_z Z3_string string);


    /**
       \brief Close interaction log.
    */
    void Z3_API Z3_close_log(__in Z3_context c);
    /*@}*/


    /**
       @name String conversion
    */
    /*@{*/

    /**
       \brief Select mode for the format used for pretty-printing AST nodes.

       The default mode for pretty printing AST nodes is to produce
       SMT-LIB style output where common subexpressions are printed 
       at each occurrence. The mode is called Z3_PRINT_SMTLIB_FULL.
       To print shared common subexpressions only once, 
       use the Z3_PRINT_LOW_LEVEL mode.
       To print in way that conforms to SMT-LIB standards and uses let
       expressions to share common sub-expressions use Z3_PRINT_SMTLIB_COMPLIANT.

       \sa Z3_ast_to_string
       \sa Z3_pattern_to_string
       \sa Z3_func_decl_to_string

    */
    void Z3_API Z3_set_ast_print_mode(__in Z3_context c, __in Z3_ast_print_mode mode);

    /**
       \brief Convert the given AST node into a string.

       \conly \warning The result buffer is statically allocated by Z3. It will
       \conly be automatically deallocated when #Z3_del_context is invoked.
       \conly So, the buffer is invalidated in the next call to \c Z3_ast_to_string.
       \sa Z3_pattern_to_string
       \sa Z3_sort_to_string
    */
    Z3_string Z3_API Z3_ast_to_string(__in Z3_context c, __in Z3_ast a);
    Z3_string Z3_API Z3_pattern_to_string(__in Z3_context c, __in Z3_pattern p);
    Z3_string Z3_API Z3_sort_to_string(__in Z3_context c, __in Z3_sort s);
    Z3_string Z3_API Z3_func_decl_to_string(__in Z3_context c, __in Z3_func_decl d);

    /**
       \brief Convert the given model into a string.

       \conly \warning The result buffer is statically allocated by Z3. It will
       \conly be automatically deallocated when #Z3_del_context is invoked.
       \conly So, the buffer is invalidated in the next call to \c Z3_model_to_string.
    */
    Z3_string Z3_API Z3_model_to_string(__in Z3_context c, __in Z3_model m);

    /**
       \brief Convert the given benchmark into SMT-LIB formatted string.

       \conly \warning The result buffer is statically allocated by Z3. It will
       \conly be automatically deallocated when #Z3_del_context is invoked.
       \conly So, the buffer is invalidated in the next call to \c Z3_benchmark_to_smtlib_string.

       \param c - context.
       \param name - name of benchmark. The argument is optional.
       \param logic - the benchmark logic. 
       \param status - the status string (sat, unsat, or unknown)
       \param attributes - other attributes, such as source, difficulty or category.
       \param num_assumptions - number of assumptions.
       \param assumptions - auxiliary assumptions.
       \param formula - formula to be checked for consistency in conjunction with assumptions.
    */
    Z3_string Z3_API Z3_benchmark_to_smtlib_string(__in   Z3_context c, 
                                                   __in_z Z3_string name,
                                                   __in_z Z3_string logic,
                                                   __in_z Z3_string status,
                                                   __in_z Z3_string attributes,
                                                   __in   unsigned num_assumptions,
                                                   __in_ecount(num_assumptions) Z3_ast assumptions[],
                                                   __in   Z3_ast formula);
    

    /**
       \brief Convert the given logical context into a string.
       
       This function is mainly used for debugging purposes. It displays
       the internal structure of a logical context.

       \conly \warning The result buffer is statically allocated by Z3. It will
       \conly be automatically deallocated when #Z3_del_context is invoked.
       \conly So, the buffer is invalidated in the next call to \c Z3_context_to_string.
    */
    Z3_string Z3_API Z3_context_to_string(__in Z3_context c);


    /**
       \brief Return runtime statistics as a string.
       
       This function is mainly used for debugging purposes. It displays
       statistics of the search activity.

       \conly \warning The result buffer is statically allocated by Z3. It will
       \conly be automatically deallocated when #Z3_del_context is invoked.
       \conly So, the buffer is invalidated in the next call to \c Z3_context_to_string.
    */
    Z3_string Z3_API Z3_statistics_to_string(__in Z3_context c);


    /**
       \brief Extract satisfying assignment from context as a conjunction.
       
       This function can be used for debugging purposes. It returns a conjunction
       of formulas that are assigned to true in the current context.
       This conjunction will contain not only the assertions that are set to true
       under the current assignment, but will also include additional literals
       if there has been a call to #Z3_check or #Z3_check_and_get_model.       
     */
    Z3_ast Z3_API Z3_get_context_assignment(__in Z3_context c);

    /*@}*/

    /**
       @name Parser interface
    */
    /*@{*/
    /**
       \brief \mlh parse_smtlib_string c str sort_names sorts decl_names decls \endmlh
       Parse the given string using the SMT-LIB parser. 
              
       The symbol table of the parser can be initialized using the given sorts and declarations. 
       The symbols in the arrays \c sort_names and \c decl_names don't need to match the names
       of the sorts and declarations in the arrays \c sorts and \c decls. This is an useful feature
       since we can use arbitrary names to reference sorts and declarations defined using the C API.

       The formulas, assumptions and declarations defined in \c str can be extracted using the functions:
       #Z3_get_smtlib_num_formulas, #Z3_get_smtlib_formula, #Z3_get_smtlib_num_assumptions, #Z3_get_smtlib_assumption, 
       #Z3_get_smtlib_num_decls, and #Z3_get_smtlib_decl.
     */
    void Z3_API Z3_parse_smtlib_string(__in Z3_context c, 
                                       __in_z Z3_string str,
                                       __in unsigned num_sorts,
                                       __in_ecount(num_sorts) Z3_symbol sort_names[],
                                       __in_ecount(num_sorts) Z3_sort sorts[],
                                       __in unsigned num_decls,
                                       __in_ecount(num_decls) Z3_symbol decl_names[],
                                       __in_ecount(num_decls) Z3_func_decl decls[]                     
                                       );
    
    /**
       \brief Similar to #Z3_parse_smtlib_string, but reads the benchmark from a file.
    */
    void Z3_API Z3_parse_smtlib_file(__in Z3_context c, 
                                     __in_z Z3_string file_name,
                                     __in unsigned num_sorts,
                                     __in_ecount(num_sorts) Z3_symbol sort_names[],
                                     __in_ecount(num_sorts) Z3_sort sorts[],
                                     __in unsigned num_decls,
                                     __in_ecount(num_decls) Z3_symbol decl_names[],
                                     __in_ecount(num_decls) Z3_func_decl decls[]  
                                     );

    /**
       \brief Return the number of SMTLIB formulas parsed by the last call to #Z3_parse_smtlib_string or #Z3_parse_smtlib_file.
    */
    unsigned Z3_API Z3_get_smtlib_num_formulas(__in Z3_context c);

    /**
       \brief \mlh get_smtlib_formula c i \endmlh
       Return the i-th formula parsed by the last call to #Z3_parse_smtlib_string or #Z3_parse_smtlib_file.

       \pre i < Z3_get_smtlib_num_formulas(c)
    */
    Z3_ast Z3_API Z3_get_smtlib_formula(__in Z3_context c, __in unsigned i);

    /**
       \brief Return the number of SMTLIB assumptions parsed by #Z3_parse_smtlib_string or #Z3_parse_smtlib_file.
    */
    unsigned Z3_API Z3_get_smtlib_num_assumptions(__in Z3_context c);

    /**
       \brief \mlh get_smtlib_assumption c i \endmlh
       Return the i-th assumption parsed by the last call to #Z3_parse_smtlib_string or #Z3_parse_smtlib_file.

       \pre i < Z3_get_smtlib_num_assumptions(c)
    */
    Z3_ast Z3_API Z3_get_smtlib_assumption(__in Z3_context c, __in unsigned i);

    /**
       \brief Return the number of declarations parsed by #Z3_parse_smtlib_string or #Z3_parse_smtlib_file.
    */
    unsigned Z3_API Z3_get_smtlib_num_decls(__in Z3_context c);

    /**
       \brief \mlh get_smtlib_decl c i \endmlh
       Return the i-th declaration parsed by the last call to #Z3_parse_smtlib_string or #Z3_parse_smtlib_file.

       \pre i < Z3_get_smtlib_num_decls(c)
    */
    Z3_func_decl Z3_API Z3_get_smtlib_decl(__in Z3_context c, __in unsigned i);

    /**
       \brief Return the number of sorts parsed by #Z3_parse_smtlib_string or #Z3_parse_smtlib_file.
    */
    unsigned Z3_API Z3_get_smtlib_num_sorts(__in Z3_context c);

    /**
       \brief \mlh get_smtlib_sort c i \endmlh
       Return the i-th sort parsed by the last call to #Z3_parse_smtlib_string or #Z3_parse_smtlib_file.

       \pre i < Z3_get_smtlib_num_sorts(c)
    */
    Z3_sort Z3_API Z3_get_smtlib_sort(__in Z3_context c, __in unsigned i);

    /**
       \brief \mlh get_smtlib_error c \endmlh
       Retrieve that last error message information generated from parsing.
    */
    Z3_string Z3_API Z3_get_smtlib_error(__in Z3_context c);

    /**
       \brief \mlh parse_z3_string c str \endmlh
       Parse the given string using the Z3 native parser.
       
       Return the conjunction of asserts made in the input.
     */
    Z3_ast Z3_API Z3_parse_z3_string(__in Z3_context c, __in_z Z3_string str);
    
    /**
       \brief Similar to #Z3_parse_z3_string, but reads the benchmark from a file.
    */
    Z3_ast Z3_API Z3_parse_z3_file(__in Z3_context c, __in_z Z3_string file_name);

    /**
       \brief \mlh parse_smtlib2_string c str \endmlh
       Parse the given string using the SMT-LIB2 parser. 
              
       It returns a formula comprising of the conjunction of assertions in the scope
       (up to push/pop) at the end of the string.
     */
    Z3_ast Z3_API Z3_parse_smtlib2_string(__in Z3_context c, 
                                          __in_z Z3_string str,
                                          __in unsigned num_sorts,
                                          __in_ecount(num_sorts) Z3_symbol sort_names[],
                                          __in_ecount(num_sorts) Z3_sort sorts[],
                                          __in unsigned num_decls,
                                          __in_ecount(num_decls) Z3_symbol decl_names[],
                                          __in_ecount(num_decls) Z3_func_decl decls[]  
                                          );
    
    /**
       \brief Similar to #Z3_parse_smtlib2_string, but reads the benchmark from a file.
    */
    Z3_ast Z3_API Z3_parse_smtlib2_file(__in Z3_context c, 
                                        __in_z Z3_string file_name,
                                          __in unsigned num_sorts,
                                          __in_ecount(num_sorts) Z3_symbol sort_names[],
                                          __in_ecount(num_sorts) Z3_sort sorts[],
                                          __in unsigned num_decls,
                                          __in_ecount(num_decls) Z3_symbol decl_names[],
                                          __in_ecount(num_decls) Z3_func_decl decls[]    
                                        );


#ifndef CAMLIDL
    /**
       \brief \mlh parse_simplify_string c str \endmlh
       Parse the given string using the Simplify parser.
       
       Return the conjunction of asserts made in the input.
     */
    Z3_ast Z3_API Z3_parse_simplify_string(__in Z3_context c, __in_z Z3_string str, __out Z3_string* parser_output);
    
    /**
       \brief Similar to #Z3_parse_simplify_string, but reads the benchmark from a file.
    */
    Z3_ast Z3_API Z3_parse_simplify_file(__in Z3_context c, __in_z Z3_string file_name, __out Z3_string* parser_output);
#endif // CAMLIDL

    /*@}*/

#ifndef CAMLIDL
    /**
       @name Error Handling
    */
    /*@{*/

    /**
       \brief Return the error code for the last API call.
       
       A call to a Z3 function may return a non Z3_OK error code,
       when it is not used correctly.

       \sa Z3_set_error_handler
    */
    Z3_error_code Z3_API Z3_get_error_code(__in Z3_context c);

    /**
       \brief Register a Z3 error handler.
       
       A call to a Z3 function may return a non Z3_OK error code, when
       it is not used correctly.  An error handler can be registered
       and will be called in this case.  To disable the use of the
       error handler, simply register with h=NULL.

       \sa Z3_get_error_code
    */
    void Z3_API Z3_set_error_handler(__in Z3_context c, __in Z3_error_handler h);
    
    /**
       \brief Set an error.
    */
    void Z3_API Z3_set_error(__in Z3_context c, __in Z3_error_code e);

    /**
       \brief Return a string describing the given error code.
     */
    Z3_string Z3_API Z3_get_error_msg(__in Z3_error_code err);
    /*@}*/

#endif // CAMLIDL

    /**
       @name Miscellaneous
    */
    /*@{*/
    
    /**
       \brief Return Z3 version number information.
    */
    void Z3_API Z3_get_version(__out unsigned * major, 
                               __out unsigned * minor, 
                               __out unsigned * build_number, 
                               __out unsigned * revision_number);


    /**
       \brief Reset all allocated resources. 

       Use this facility on out-of memory errors. 
       It allows discharging the previous state and resuming afresh.
       Any pointers previously returned by the API
       become invalid.
    */
    void Z3_API Z3_reset_memory(void);
    
    /*@}*/

    /** 
        @name External Theory Plugins
    */
    /*@{*/
    
#ifndef CAMLIDL

    //
    // callbacks and void* don't work with CAMLIDL.
    // 
    typedef Z3_bool Z3_reduce_eq_callback_fptr(__in Z3_theory t, __in Z3_ast a, __in Z3_ast b, __out Z3_ast * r);

    typedef Z3_bool Z3_reduce_app_callback_fptr(__in Z3_theory, __in Z3_func_decl, __in unsigned, __in Z3_ast const [], __out Z3_ast *);


    typedef Z3_bool Z3_reduce_distinct_callback_fptr(__in Z3_theory, __in unsigned, __in Z3_ast const [], __out Z3_ast *);

    typedef void Z3_theory_callback_fptr(__in Z3_theory t);
    
    typedef Z3_bool Z3_theory_final_check_callback_fptr(__in Z3_theory);
    
    typedef void Z3_theory_ast_callback_fptr(__in Z3_theory, __in Z3_ast);
    
    typedef void Z3_theory_ast_bool_callback_fptr(__in Z3_theory, __in Z3_ast, __in Z3_bool);
    
    typedef void Z3_theory_ast_ast_callback_fptr(__in Z3_theory, __in Z3_ast, __in Z3_ast);


    /**
       \brief Create a new user defined theory. The new theory will be identified by the name \c th_name.
       A theory must be created before asserting any assertion to the given context.
       Return NULL in case of failure.

       \c data is a pointer to an external data-structure that may be used to store
       theory specific additional data.
    */
    Z3_theory Z3_API Z3_mk_theory(__in Z3_context c, __in_z Z3_string th_name, __in Z3_theory_data data);

    /**
       \brief Return a pointer to the external data-structure supplied to the function #Z3_mk_theory.

       \see Z3_mk_theory
    */
    Z3_theory_data Z3_API Z3_theory_get_ext_data(__in Z3_theory t);

#endif
    
    /**
       \brief Create an interpreted theory sort.
    */
    Z3_sort Z3_API Z3_theory_mk_sort(__in Z3_context c, __in Z3_theory t, __in Z3_symbol s);
    
    /**
       \brief Create an interpreted theory constant value. Values are assumed to be different from each other.
    */
    Z3_ast Z3_API Z3_theory_mk_value(__in Z3_context c, __in Z3_theory t, __in Z3_symbol n, __in Z3_sort s);

    /**
       \brief Create an interpreted constant for the given theory.
    */
    Z3_ast Z3_API Z3_theory_mk_constant(__in Z3_context c, __in Z3_theory t, __in Z3_symbol n, __in Z3_sort s);
    
    /**
       \brief Create an interpreted function declaration for the given theory.
    */
    Z3_func_decl Z3_API Z3_theory_mk_func_decl(__in Z3_context c, __in Z3_theory t, __in Z3_symbol n,
                                               __in unsigned domain_size, __in_ecount(domain_size) Z3_sort const domain[],
                                               __in Z3_sort range);

    /**
       \brief Return the context where the given theory is installed.
    */
    Z3_context Z3_API Z3_theory_get_context(__in Z3_theory t);



#ifndef CAMLIDL
    /**
       \brief Set a callback that is invoked when theory \c t is deleted.
       This callback should be used to delete external data-structures associated with the given theory.

       The callback has the form <tt>f(t)</tt>, where
       - \c t is the given theory
       
       \see Z3_mk_theory 
       \see Z3_theory_get_ext_data
    */
    void Z3_API Z3_set_delete_callback(__in Z3_theory t, __in Z3_theory_callback_fptr f);
    
    /**
       \brief Set a callback for simplifying operators of the given theory.
       The callback \c f is invoked by Z3's simplifier.

       It is of the form <tt>f(t, d, n, args, r)</tt>, where:
         - \c t is the given theory
         - \c d is the declaration of the theory operator
         - \c n is the number of arguments in the array \c args
         - \c args are arguments for the theory operator
         - \c r should contain the result: an expression equivalent to <tt>d(args[0], ..., args[n-1])</tt>.

      If <tt>f(t, d, n, args, r)</tt> returns false, then \c r is ignored, and Z3 assumes that no simplification was performed.
    */
    void Z3_API Z3_set_reduce_app_callback(__in Z3_theory t, __in Z3_reduce_app_callback_fptr f);
    
    /**
       \brief Set a callback for simplifying the atom <tt>s_1 = s_2</tt>, when the
       sort of \c s_1 and \c s_2 is an interpreted sort of the given theory.
       The callback \c f is invoked by Z3's simplifier.
       
       It has the form <tt>f(t, s_1, s_2, r)</tt>, where:
         - \c t is the given theory
         - \c s_1 is the left-hand-side
         - \c s_2 is the right-hand-side
         - \c r should contain the result: an expression equivalent to <tt>s_1 = s_2</tt>.
         
       If <tt>f(t, s_1, s_2, r)</tt> returns false, then \c r is ignored, and Z3 assumes that no simplification was performed.
    */
    void Z3_API Z3_set_reduce_eq_callback(__in Z3_theory t, __in Z3_reduce_eq_callback_fptr f);

    /**
       \brief Set a callback for simplifying the atom <tt>distinct(s_1, ..., s_n)</tt>, when the
       sort of \c s_1, ..., \c s_n is an interpreted sort of the given theory.
       The callback \c f is invoked by Z3's simplifier.
       
       It has the form <tt>f(t, n, args, r)</tt>, where:
         - \c t is the given theory
         - \c n is the number of arguments in the array \c args
         - \c args are arguments for distinct.
         - \c r should contain the result: an expression equivalent to <tt>distinct(s_1, ..., s_n)</tt>.
         
       If <tt>f(t, n, args, r)</tt> returns false, then \c r is ignored, and Z3 assumes that no simplification was performed.
    */
    void Z3_API Z3_set_reduce_distinct_callback(__in Z3_theory t, __in Z3_reduce_distinct_callback_fptr f);
    
    /**
       \brief Set a callback that is invoked when a theory application
       is finally added into the logical context. Note that, not every
       application contained in an asserted expression is actually
       added into the logical context because it may be simplified
       during a preprocessing step.
    
       The callback has the form <tt>f(t, n)</tt>, where
       - \c t is the given theory
       
       - \c n is a theory application, that is, an expression of the form <tt>g(...)</tt> where \c g is a theory operator.

       \remark An expression \c n added to the logical context at search level \c n,
       will remain in the logical context until this level is backtracked.
    */
    void Z3_API Z3_set_new_app_callback(__in Z3_theory t, __in Z3_theory_ast_callback_fptr f);

    /**
       \brief Set a callback that is invoked when an expression of
       sort \c s, where \c s is an interpreted sort of the theory \c
       t, is finally added into the logical context. Note that, not
       every expression contained in an asserted expression is
       actually added into the logical context because it may be
       simplified during a preprocessing step.

       The callback has the form <tt>f(t, n)</tt>, where
       - \c t is the given theory
       
       - \c n is an expression of sort \c s, where \c s is an interpreted sort of \c t.

       \remark An expression \c n added to the logical context at search level \c n,
       will remain in the logical context until this level is backtracked.
    */
    void Z3_API Z3_set_new_elem_callback(__in Z3_theory t, __in Z3_theory_ast_callback_fptr f);

    /**
       \brief Set a callback that is invoked when Z3 starts searching for a
       satisfying assignment.
       
       The callback has the form <tt>f(t)</tt>, where
       - \c t is the given theory
    */
    void Z3_API Z3_set_init_search_callback(__in Z3_theory t, __in Z3_theory_callback_fptr f);
        
    /**
       \brief Set a callback that is invoked when Z3 creates a
       case-split (aka backtracking point). 

       When a case-split is created we say the search level is increased.
       
       The callback has the form <tt>f(t)</tt>, where
       - \c t is the given theory
    */
    void Z3_API Z3_set_push_callback(__in Z3_theory t, __in Z3_theory_callback_fptr f);
 
    /**
       \brief Set a callback that is invoked when Z3 backtracks a
       case-split.

       When a case-split is backtracked we say the search level is decreased.
       
       The callback has the form <tt>f(t)</tt>, where
       - \c t is the given theory
    */
    void Z3_API Z3_set_pop_callback(__in Z3_theory t, __in Z3_theory_callback_fptr f);

    /**
       \brief Set a callback that is invoked when Z3 restarts the
       search for a satisfying assignment.
       
       The callback has the form <tt>f(t)</tt>, where
       - \c t is the given theory
    */
    void Z3_API Z3_set_restart_callback(__in Z3_theory t, __in Z3_theory_callback_fptr f);

    /**
       \brief Set a callback that is invoked when the logical context
       is reset by the user. This callback is useful for reseting any
       data-structure maintained by the user theory solver.
       
       The callback has the form <tt>f(t)</tt>, where
       - \c t is the given theory
    */
    void Z3_API Z3_set_reset_callback(__in Z3_theory t, __in Z3_theory_callback_fptr f);

    /**
       \brief Set a callback that is invoked before Z3 starts building a model.
       A theory may use this callback to perform expensive operations.

       The callback has the form <tt>f(t)</tt>, where
       - \c t is the given theory

       If the theory return \c Z3_false, Z3 will assume that theory is giving up,
       and it will assume that it was not possible to decide if the asserted constraints
       are satisfiable or not.
    */
    void Z3_API Z3_set_final_check_callback(__in Z3_theory t, __in Z3_theory_final_check_callback_fptr f);

    /**
       \brief Set a callback that is invoked when an equality <tt>s_1 = s_2</tt>
       is found by the logical context.

       The callback has the form <tt>f(t, s_1, s_2)</tt>, where:
         - \c t is the given theory
         - \c s_1 is the left-hand-side
         - \c s_2 is the right-hand-side
    */
    void Z3_API Z3_set_new_eq_callback(__in Z3_theory t, __in Z3_theory_ast_ast_callback_fptr f);

    /**
       \brief Set a callback that is invoked when a disequality <tt>s_1 != s_2</tt>
       is found by the logical context.

       The callback has the form <tt>f(t, s_1, s_2)</tt>, where:
         - \c t is the given theory
         - \c s_1 is the left-hand-side
         - \c s_2 is the right-hand-side
    */
    void Z3_API Z3_set_new_diseq_callback(__in Z3_theory t, __in Z3_theory_ast_ast_callback_fptr f);

    /**
       \brief Set a callback that is invoked when a theory predicate is assigned to true/false by Z3.
       
       The callback has the form <tt>f(t, p, v)</tt>, where:
         - \c t is the given theory
         - \c p is the assigned predicate.
         - \c v is the value (true/false) assigned to \c p.
    */
    void Z3_API Z3_set_new_assignment_callback(__in Z3_theory t, __in Z3_theory_ast_bool_callback_fptr f);

    /**
       \brief Set a callback that is invoked when an expression is
       marked as relevant during the search. This callback is only
       invoked when relevancy propagation is enabled.
       
       The callback has the form <tt>f(t, n)</tt>, where:
         - \c t is the given theory
         - \c n is the relevant expression
    */
    void Z3_API Z3_set_new_relevant_callback(__in Z3_theory t, __in Z3_theory_ast_callback_fptr f);

#endif // CAMLIDL
    /**
       \brief Assert a theory axiom/lemmas during the search.
       
       An axiom added at search level \c n will remain in the logical context until 
       level \c n is backtracked. 

       The callbacks for push (#Z3_set_push_callback) and pop
       (#Z3_set_pop_callback) can be used to track when the search
       level is increased (i.e., new case-split) and decreased (i.e.,
       case-split is backtracked).
       
       Z3 tracks the theory axioms asserted. So, multiple assertions of the same axiom are
       ignored.
    */
    void Z3_API Z3_theory_assert_axiom(__in Z3_theory t, __in Z3_ast ax);

    /**
       \brief Inform to the logical context that \c lhs and \c rhs have the same interpretation
       in the model being built by theory \c t. If lhs = rhs is inconsistent with other theories,
       then the logical context will backtrack.

       For more information, see the paper "Model-Based Theory Combination" in the Z3 website.
    */
    void Z3_API Z3_theory_assume_eq(__in Z3_theory t, __in Z3_ast lhs, __in Z3_ast rhs);

    /**
       \brief Enable/disable the simplification of theory axioms asserted using #Z3_theory_assert_axiom.
       By default, the simplification of theory specific operators is disabled. 
       That is, the reduce theory callbacks are not invoked for theory axioms.
       The default behavior is useful when asserting axioms stating properties of theory operators.
    */
    void Z3_API Z3_theory_enable_axiom_simplification(__in Z3_theory t, __in Z3_bool flag);

    /**
       \brief Return the root of the equivalence class containing \c n.
    */
    Z3_ast Z3_API Z3_theory_get_eqc_root(__in Z3_theory t, __in Z3_ast n);
    
    /**
       \brief Return the next element in the equivalence class containing \c n.

       The elements in an equivalence class are organized in a circular list.
       You can traverse the list by calling this function multiple times 
       using the result from the previous call. This is illustrated in the
       code snippet below.
       \code
           Z3_ast curr = n;
           do
             curr = Z3_theory_get_eqc_next(theory, curr);
           while (curr != n);
       \endcode
    */
    Z3_ast Z3_API Z3_theory_get_eqc_next(__in Z3_theory t, __in Z3_ast n);

    /**
       \brief Return the number of parents of \c n that are operators of the given theory. 
    */
    unsigned Z3_API Z3_theory_get_num_parents(__in Z3_theory t, __in Z3_ast n);
    
    /**
       \brief Return the i-th parent of \c n. 
       See #Z3_theory_get_num_parents. 
    */
    Z3_ast Z3_API Z3_theory_get_parent(__in Z3_theory t, __in Z3_ast n, __in unsigned i);

    /**
       \brief Return \c Z3_TRUE if \c n is an interpreted theory value.
    */
    Z3_bool Z3_API Z3_theory_is_value(__in Z3_theory t, __in Z3_ast n);

    /**
       \brief Return \c Z3_TRUE if \c d is an interpreted theory declaration.
    */
    Z3_bool Z3_API Z3_theory_is_decl(__in Z3_theory t, __in Z3_func_decl d);
    
    /**
       \brief Return the number of expressions of the given theory in
       the logical context. These are the expressions notified using the
       callback #Z3_set_new_elem_callback.
    */
    unsigned Z3_API Z3_theory_get_num_elems(__in Z3_theory t);
    
    /**
       \brief Return the i-th elem of the given theory in the logical context.
       
       \see Z3_theory_get_num_elems
    */
    Z3_ast Z3_API Z3_theory_get_elem(__in Z3_theory t, __in unsigned i);

    /**
       \brief Return the number of theory applications in the logical
       context. These are the expressions notified using the callback
       #Z3_set_new_app_callback.
    */
    unsigned Z3_API Z3_theory_get_num_apps(__in Z3_theory t);
    
    /**
       \brief Return the i-th application of the given theory in the logical context.
       
       \see Z3_theory_get_num_apps
    */
    Z3_ast Z3_API Z3_theory_get_app(__in Z3_theory t, __in unsigned i);

    /*@}*/

    
    /** 
        @name Fixedpoint and Datalog facilities
    */
    /*@{*/
    /** 
       \brief Add a universal Horn clause as a named rule.
       The \c horn_rule should be of the form:
 
       \code
           horn_rule ::= (forall (bound-vars) horn_rule)
                      |  (=> atoms horn_rule)
                      |  atom
       \endcode
    */
    void Z3_API Z3_datalog_add_rule(__in Z3_context c, __in Z3_ast horn_rule, __in Z3_symbol name);
    
    /** 
        \brief Pose a query against the asserted rules.

        The query returns a formula that encodes the set of
        satisfying instances for the query.

        \code
           query ::= (exists (bound-vars) query)
                 |  literals 
        \endcode

    */
    Z3_ast Z3_API Z3_datalog_query(__in Z3_context c,  __in Z3_ast q);

    /**
       \brief Configure the predicate representation.

       It sets the predicate to use a set of domains given by the list of symbols.
       The domains given by the list of symbols must belong to a set
       of built-in domains.
    */

    void Z3_API Z3_datalog_set_predicate_representation(
        __in Z3_context c, __in Z3_func_decl f, 
        __in unsigned num_relations, 
        __in_ecount(num_relations) Z3_symbol const relation_kinds[]);

    /**
         \brief Parse a file in Datalog format and process the queries in it.
    */
    void Z3_API Z3_datalog_parse_file(__in Z3_context c, Z3_string filename);

    /**
         \brief The following utilities allows adding user-defined domains.
    */

#ifndef CAMLIDL
    typedef void Z3_datalog_reduce_assign_callback_fptr(
        __in Z3_context, __in Z3_func_decl, 
        __in unsigned, __in Z3_ast const [], 
        __in unsigned, __in Z3_ast const []); 

    typedef void Z3_datalog_reduce_app_callback_fptr(
        __in Z3_context, __in Z3_func_decl, 
        __in unsigned, __in Z3_ast const [], 
        __out Z3_ast*);


    /**
         \brief Initialize the context with a user-defined state.

    */
    void Z3_API Z3_datalog_init(__in Z3_context c, __in void* state);

    /**
         \brief Retrieve the user-define state.
    */
    void* Z3_API Z3_datalog_get_context(__in Z3_context c);
    

    /**
         \brief Register a callback to destructive updates.

         Registers are identified with terms encoded as fresh constants,          
    */
    void Z3_API Z3_datalog_set_reduce_assign_callback(
        __in Z3_context c, __in Z3_datalog_reduce_assign_callback_fptr cb);

    /**
         \brief Register a callback for buildling terms based on 
         the relational operators.
    */
    void Z3_API Z3_datalog_set_reduce_app_callback(
        __in Z3_context c, __in Z3_datalog_reduce_app_callback_fptr cb);

#endif

    /*@}*/
    
#ifndef CAMLIDL
#ifdef __cplusplus
};
#endif // __cplusplus
#else
}
#endif // CAMLIDL

/*@}*/
