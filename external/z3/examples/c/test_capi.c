#include<stdio.h>
#include<stdlib.h>
#include<stdarg.h>
#include<memory.h>
#include<setjmp.h>
#include<z3.h>

/** 
   \defgroup capi_ex C API examples
*/
/*@{*/
/**
   @name Auxiliary Functions
*/
/*@{*/

/**
   \brief exit gracefully in case of error.
*/
void exitf(const char* message) 
{
  fprintf(stderr,"BUG: %s.\n", message);
  exit(1);
}

/**
   \brief exit if unreachable code was reached.
*/
void unreachable() 
{
    exitf("unreachable code was reached");
}

/**
   \brief Simpler error handler.
 */
void error_handler(Z3_error_code e) 
{
  exitf("incorrect use of Z3");
}

static jmp_buf g_catch_buffer;
/**
   \brief Low tech exceptions. 
   
   In high-level programming languages, an error handler can throw an exception.
*/
void throw_z3_error(Z3_error_code c) 
{
    longjmp(g_catch_buffer, c);
}

/**
   \brief Create a logical context.  

   Enable model construction. Other configuration parameters can be passed in the cfg variable.

   Also enable tracing to stderr and register custom error handler.
*/
Z3_context mk_context_custom(Z3_config cfg, Z3_error_handler err) 
{
    Z3_context ctx;
    
    Z3_set_param_value(cfg, "MODEL", "true");
    ctx = Z3_mk_context(cfg);
#ifdef TRACING
    Z3_trace_to_stderr(ctx);
#endif
    Z3_set_error_handler(ctx, err);
    
    return ctx;
}

/**
   \brief Create a logical context.

   Enable model construction only.

   Also enable tracing to stderr and register standard error handler.
*/
Z3_context mk_context() 
{
    Z3_config  cfg;
    Z3_context ctx;
    cfg = Z3_mk_config();
    ctx = mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);
    return ctx;
}

/**
   \brief Create a variable using the given name and type.
*/
Z3_ast mk_var(Z3_context ctx, const char * name, Z3_type_ast ty) 
{
    Z3_symbol   s  = Z3_mk_string_symbol(ctx, name);
    return Z3_mk_const(ctx, s, ty);
}

/**
   \brief Create a boolean variable using the given name.
*/
Z3_ast mk_bool_var(Z3_context ctx, const char * name) 
{
    Z3_type_ast ty = Z3_mk_bool_type(ctx);
    return mk_var(ctx, name, ty);
}

/**
   \brief Create an integer variable using the given name.
*/
Z3_ast mk_int_var(Z3_context ctx, const char * name) 
{
    Z3_type_ast ty = Z3_mk_int_type(ctx);
    return mk_var(ctx, name, ty);
}

/**
   \brief Create a Z3 integer node using a C int. 
*/
Z3_ast mk_int(Z3_context ctx, int v) 
{
    Z3_type_ast ty = Z3_mk_int_type(ctx);
    return Z3_mk_int(ctx, v, ty);
}

/**
   \brief Create a real variable using the given name.
*/
Z3_ast mk_real_var(Z3_context ctx, const char * name) 
{
    Z3_type_ast ty = Z3_mk_real_type(ctx);
    return mk_var(ctx, name, ty);
}

/**
   \brief Create the unary function application: <tt>(f x)</tt>.
*/
Z3_ast mk_unary_app(Z3_context ctx, Z3_const_decl_ast f, Z3_ast x) 
{
    Z3_ast args[1] = {x};
    return Z3_mk_app(ctx, f, 1, args);
}

/**
   \brief Create the binary function application: <tt>(f x y)</tt>.
*/
Z3_ast mk_binary_app(Z3_context ctx, Z3_const_decl_ast f, Z3_ast x, Z3_ast y) 
{
    Z3_ast args[2] = {x, y};
    return Z3_mk_app(ctx, f, 2, args);
}

/**
   \brief Check whether the logical context is satisfiable, and compare the result with the expected result.
   If the context is satisfiable, then display the model.
*/
void check(Z3_context ctx, Z3_lbool expected_result)
{
    Z3_model m      = 0;
    Z3_lbool result = Z3_check_and_get_model(ctx, &m);
    switch (result) {
    case Z3_L_FALSE:
        printf("unsat\n");
        break;
    case Z3_L_UNDEF:
        printf("unknown\n");
        printf("potential model:\n%s\n", Z3_model_to_string(ctx, m));
        break;
    case Z3_L_TRUE:
        printf("sat\n%s\n", Z3_model_to_string(ctx, m));
        break;
    }
    if (m) {
        Z3_del_model(m);
    }
    if (result != expected_result) {
        exitf("unexpected result");
    }
}

/**
   \brief Prove that the constraints already asserted into the logical
   context implies the given formula.  The result of the proof is
   displayed.
   
   Z3 is a satisfiability checker. So, one can prove \c f by showing
   that <tt>(not f)</tt> is unsatisfiable.

   The context \c ctx is not modified by this function.
*/
void prove(Z3_context ctx, Z3_ast f, Z3_bool is_valid)
{
    Z3_model m;
    Z3_ast   not_f;

    /* save the current state of the context */
    Z3_push(ctx);

    not_f = Z3_mk_not(ctx, f);
    Z3_assert_cnstr(ctx, not_f);
    
    m = 0;
    
    switch (Z3_check_and_get_model(ctx, &m)) {
    case Z3_L_FALSE:
        /* proved */
        printf("valid\n");
        if (!is_valid) {
            exitf("unexpected result");
        }
        break;
    case Z3_L_UNDEF:
        /* Z3 failed to prove/disprove f. */
        printf("unknown\n");
        if (m != 0) {
            /* m should be viewed as a potential counterexample. */
            printf("potential counterexample:\n%s\n", Z3_model_to_string(ctx, m));
        }
        if (is_valid) {
            exitf("unexpected result");
        }
        break;
    case Z3_L_TRUE:
        /* disproved */
        printf("invalid\n");
        if (m) {
            /* the model returned by Z3 is a counterexample */
            printf("counterexample:\n%s\n", Z3_model_to_string(ctx, m));
        }
        if (is_valid) {
            exitf("unexpected result");
        }
        break;
    }

    if (m) {
        Z3_del_model(m);
    }

    /* restore context */
    Z3_pop(ctx, 1);
}

/**
   \brief Assert the axiom: function f is injective in the i-th argument.
   
   The following axiom is asserted into the logical context:
   \code
   forall (x_0, ..., x_n) finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i
   \endcode

   Where, \c finv is a fresh function declaration.
*/
void assert_inj_axiom(Z3_context ctx, Z3_const_decl_ast f, unsigned i) 
{
    unsigned sz, j;
    Z3_type_ast finv_domain, finv_range;
    Z3_const_decl_ast finv;
    Z3_type_ast * types; /* types of the quantified variables */
    Z3_symbol *   names; /* names of the quantified variables */
    Z3_ast * xs;         /* arguments for the application f(x_0, ..., x_i, ..., x_{n-1}) */
    Z3_ast   x_i, fxs, finv_fxs, eq;
    Z3_pattern_ast p;
    Z3_ast   q;
    sz = Z3_get_domain_size(ctx, f);

    if (i >= sz) {
        exitf("failed to create inj axiom");
    }
    
    /* declare the i-th inverse of f: finv */
    finv_domain = Z3_get_range(ctx, f);
    finv_range  = Z3_get_domain(ctx, f, i);
    finv        = Z3_mk_fresh_func_decl(ctx, "inv", 1, &finv_domain, finv_range);

    /* allocate temporary arrays */
    types       = (Z3_type_ast *) malloc(sizeof(Z3_type_ast) * sz);
    names       = (Z3_symbol *) malloc(sizeof(Z3_symbol) * sz);
    xs          = (Z3_ast *) malloc(sizeof(Z3_ast) * sz);
    
    /* fill types, names and xs */
    for (j = 0; j < sz; j++) { types[j] = Z3_get_domain(ctx, f, j); };
    for (j = 0; j < sz; j++) { names[j] = Z3_mk_int_symbol(ctx, j); };
    for (j = 0; j < sz; j++) { xs[j]    = Z3_mk_bound(ctx, j, types[j]); };

    x_i = xs[i];

    /* create f(x_0, ..., x_i, ..., x_{n-1}) */ 
    fxs         = Z3_mk_app(ctx, f, sz, xs);

    /* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) */
    finv_fxs    = mk_unary_app(ctx, finv, fxs);

    /* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i */
    eq          = Z3_mk_eq(ctx, finv_fxs, x_i);

    /* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier */
    p           = Z3_mk_pattern(ctx, 1, &fxs);
    printf("pattern: %s\n", Z3_ast_to_string(ctx, Z3_pattern_ast_to_ast(ctx, p)));
    printf("\n");

    /* create & assert quantifier */
    q           = Z3_mk_forall(ctx, 
                                 0, /* using default weight */
                                 1, /* number of patterns */
                                 &p, /* address of the "array" of patterns */
                                 sz, /* number of quantified variables */
                                 types, 
                                 names,
                                 eq);
    printf("assert axiom:\n%s\n", Z3_ast_to_string(ctx, q));
    Z3_assert_cnstr(ctx, q);

    /* free temporary arrays */
    free(types);
    free(names);
    free(xs);
}

/**
   \brief Assert the axiom: function f is commutative. 
   
   This example uses the SMT-LIB parser to simplify the axiom construction.
*/
void assert_comm_axiom(Z3_context ctx, Z3_const_decl_ast f) 
{
    Z3_type_ast t;
    Z3_symbol f_name, t_name;
    Z3_ast q;

    t = Z3_get_range(ctx, f);

    if (Z3_get_domain_size(ctx, f) != 2 ||
        Z3_get_domain(ctx, f, 0) != t ||
        Z3_get_domain(ctx, f, 1) != t) {
        exitf("function must be binary, and argument types must be equal to return type");
    } 
    
    /* Inside the parser, function f will be referenced using the symbol 'f'. */
    f_name = Z3_mk_string_symbol(ctx, "f");
    
    /* Inside the parser, type t will be referenced using the symbol 'T'. */
    t_name = Z3_mk_string_symbol(ctx, "T");

    Z3_parse_smtlib_string(ctx, 
                           "(benchmark comm :formula (forall (x T) (y T) (= (f x y) (f y x))))",
                           1, &t_name, &t,
                           1, &f_name, &f);
    q = Z3_get_smtlib_formula(ctx, 0);
    printf("assert axiom:\n%s\n", Z3_ast_to_string(ctx, q));
    Z3_assert_cnstr(ctx, q);
}

/**
   \brief Z3 does not support explicitly tuple updates. They can be easily implemented 
   as macros. The argument \c t must have tuple type. 
   A tuple update is a new tuple where field \c i has value \c new_val, and all
   other fields have the value of the respective field of \c t.

   <tt>update(t, i, new_val)</tt> is equivalent to
   <tt>mk_tuple(proj_0(t), ..., new_val, ..., proj_n(t))</tt> 
*/
Z3_ast mk_tuple_update(Z3_context c, Z3_ast t, unsigned i, Z3_ast new_val) 
{
    Z3_type_ast         ty;
    Z3_const_decl_ast   mk_tuple_decl;
    unsigned            num_fields, j;
    Z3_ast *            new_fields;
    Z3_ast              result;

    ty = Z3_get_type(c, t);

    if (Z3_get_type_kind(c, ty) != Z3_TUPLE_TYPE) {
        exitf("argument must be a tuple");
    }

    num_fields = Z3_get_tuple_type_num_fields(c, ty);
    
    if (i >= num_fields) {
        exitf("invalid tuple update, index is too big");
    }
    
    new_fields = (Z3_ast*) malloc(sizeof(Z3_ast) * num_fields);
    for (j = 0; j < num_fields; j++) {
        if (i == j) {
            /* use new_val at position i */
            new_fields[j] = new_val;
        }
        else {
            /* use field j of t */
            Z3_const_decl_ast proj_decl = Z3_get_tuple_type_field_decl(c, ty, j);
            new_fields[j] = mk_unary_app(c, proj_decl, t);
        }
    }
    mk_tuple_decl = Z3_get_tuple_type_mk_decl(c, ty);
    result = Z3_mk_app(c, mk_tuple_decl, num_fields, new_fields);
    free(new_fields);
    return result;
}

/**
   \brief Display a symbol in the given output stream.
*/
void display_symbol(Z3_context c, FILE * out, Z3_symbol s) 
{
    switch (Z3_get_symbol_kind(c, s)) {
    case Z3_INT_SYMBOL:
        fprintf(out, "#%d", Z3_get_symbol_int(c, s));
        break;
    case Z3_STRING_SYMBOL:
        fprintf(out, Z3_get_symbol_string(c, s));
        break;
    default:
        unreachable();
    }
}

/**
   \brief Display the given type.
*/
void display_type(Z3_context c, FILE * out, Z3_type_ast ty) 
{
    switch (Z3_get_type_kind(c, ty)) {
    case Z3_UNINTERPRETED_TYPE:
        display_symbol(c, out, Z3_get_type_name(c, ty));
        break;
    case Z3_BOOL_TYPE:
        fprintf(out, "bool");
        break;
    case Z3_INT_TYPE:
        fprintf(out, "int");
        break;
    case Z3_REAL_TYPE:
        fprintf(out, "real");
        break;
    case Z3_BV_TYPE:
        fprintf(out, "bv%d", Z3_get_bv_type_size(c, ty));
        break;
    case Z3_ARRAY_TYPE: 
        fprintf(out, "[");
        display_type(c, out, Z3_get_array_type_domain(c, ty));
        fprintf(out, "->");
        display_type(c, out, Z3_get_array_type_range(c, ty));
        fprintf(out, "]");
        break;
    case Z3_TUPLE_TYPE: {
        unsigned num_fields = Z3_get_tuple_type_num_fields(c, ty);
        unsigned i;
        fprintf(out, "(");
        for (i = 0; i < num_fields; i++) {
            Z3_const_decl_ast field = Z3_get_tuple_type_field_decl(c, ty, i);
            if (i > 0) {
                fprintf(out, ", ");
            }
            display_type(c, out, Z3_get_range(c, field));
        }
        fprintf(out, ")");
        break;
    }
    default:
        fprintf(out, "unknown[");
        display_symbol(c, out, Z3_get_type_name(c, ty));
        fprintf(out, "]");
        break;
    }
}

/**
   \brief Custom value pretty printer. 

   This function demonstrates how to use the API to navigate values 
   found in Z3 models.
*/
void display_value(Z3_context c, FILE * out, Z3_value v) 
{
    switch (Z3_get_value_kind(c, v)) {
    case Z3_BOOL_VALUE:
        fprintf(out, Z3_get_bool_value_bool(c, v) ? "true" : "false");
        break;
    case Z3_NUMERAL_VALUE: {
        Z3_type_ast t;
        fprintf(out, Z3_get_numeral_value_string(c, v));
        t = Z3_get_value_type(c, v);
        fprintf(out, ":");
        display_type(c, out, t);
        break;
    }
    case Z3_TUPLE_VALUE: {
        unsigned i;
        unsigned num_fields = Z3_get_tuple_value_num_fields(c, v);
        fprintf(out, "[");
        for (i = 0; i < num_fields; i++) {
            if (i > 0) {
                fprintf(out, ", ");
            }
            display_value(c, out, Z3_get_tuple_value_field(c, v, i));
        }
        fprintf(out, "]");
        break;
    }
    case Z3_ARRAY_VALUE: {
        unsigned i;
        unsigned array_size = Z3_get_array_value_size(c, v);
        fprintf(out, "{");
        for (i = 0; i < array_size; i++) {
            if (i > 0) {
                fprintf(out, ", ");
            }
            fprintf(out, "(");
            display_value(c, out, Z3_get_array_value_entry_index(c, v, i));
            fprintf(out, "|->");
            display_value(c, out, Z3_get_array_value_entry_value(c, v, i));
            fprintf(out, ")");
        }
        if (array_size > 0) {
            fprintf(out, ", ");
        }
        fprintf(out, "(else|->");
        display_value(c, out, Z3_get_array_value_else(c, v));
        fprintf(out, ")}");
        break;
    }
    default:
        fprintf(out, "#unknown");
    }
}

/**
   \brief Custom function interpretations pretty printer.
*/
void display_function_interpretations(Z3_context c, FILE * out, Z3_model m) 
{
    unsigned num_functions, i;

    fprintf(out, "function interpretations:\n");

    num_functions = Z3_get_model_num_funcs(c, m);
    for (i = 0; i < num_functions; i++) {
        if (!Z3_is_model_func_internal(c, m, i)) {
            Z3_const_decl_ast fdecl;
            Z3_symbol name;
            Z3_value func_else;
            unsigned num_entries, j;

            fdecl = Z3_get_model_func_decl(c, m, i);
            name = Z3_get_decl_name(c, fdecl);
            display_symbol(c, out, name);
            fprintf(out, " = {");
            num_entries = Z3_get_model_func_num_entries(c, m, i);
            for (j = 0; j < num_entries; j++) {
                unsigned num_args, k;
                if (j > 0) {
                    fprintf(out, ", ");
                }
                num_args = Z3_get_model_func_entry_num_args(c, m, i, j);
                fprintf(out, "(");
                for (k = 0; k < num_args; k++) {
                    if (k > 0) {
                        fprintf(out, ", ");
                    }
                    display_value(c, out, Z3_get_model_func_entry_arg(c, m, i, j, k));
                }
                fprintf(out, "|->");
                display_value(c, out, Z3_get_model_func_entry_value(c, m, i, j));
                fprintf(out, ")");
            }
            if (num_entries > 0) {
                fprintf(out, ", ");
            }
            fprintf(out, "(else|->");
            func_else = Z3_get_model_func_else(c, m, i);
            display_value(c, out, func_else);
            fprintf(out, ")}\n");
        }
    }
}

/**
   \brief Custom model pretty printer.
*/
void display_model(Z3_context c, FILE * out, Z3_model m) 
{
    unsigned num_constants;
    unsigned i;

    num_constants = Z3_get_model_num_constants(c, m);
    for (i = 0; i < num_constants; i++) {
        Z3_symbol name;
        Z3_const_decl_ast cnst = Z3_get_model_constant(c, m, i);
        name = Z3_get_decl_name(c, cnst);
        display_symbol(c, out, name);
        fprintf(out, " = ");
        display_value(c, out, Z3_get_value(c, m, cnst));
        fprintf(out, "\n");
    }
    display_function_interpretations(c, out, m);
}

/**
   \brief Similar to #check, but uses #display_model instead of #Z3_model_to_string.
*/
void check2(Z3_context ctx, Z3_lbool expected_result)
{
    Z3_model m      = 0;
    Z3_lbool result = Z3_check_and_get_model(ctx, &m);
    switch (result) {
    case Z3_L_FALSE:
        printf("unsat\n");
        break;
    case Z3_L_UNDEF:
        printf("unknown\n");
        printf("potential model:\n");
        display_model(ctx, stdout, m);
        break;
    case Z3_L_TRUE:
        printf("sat\n");
        display_model(ctx, stdout, m);
        break;
    }
    if (m) {
        Z3_del_model(m);
    }
    if (result != expected_result) {
        exitf("unexpected result");
    }
}

/**
   \brief Display Z3 version in the standard output.
*/
void display_version() 
{
    unsigned major, minor, build, revision;
    Z3_get_version(&major, &minor, &build, &revision);
    printf("Z3 %d.%d.%d.%d\n", major, minor, build, revision);
}
/*@}*/

/**
   @name Examples
*/
/*@{*/
/**
   \brief "Hello world" example: create a Z3 logical context, and delete it.
*/
void simple_example() 
{
    Z3_context ctx;
    
    printf("\nsimple_example\n");
 
    ctx = mk_context();

    /* do something with the context */
    printf("CONTEXT:\n%sEND OF CONTEXT\n", Z3_context_to_string(ctx));

    /* delete logical context */
    Z3_del_context(ctx);
}

/**
  Demonstration of how Z3 can be used to prove validity of
  De Morgan's Duality Law: {e not(x and y) <-> (not x) or ( not y) }
*/
void demorgan() 
{
    Z3_config cfg;
    Z3_context ctx;
    Z3_type_ast bool_type;
    Z3_symbol symbol_x, symbol_y;
    Z3_ast x, y, not_x, not_y, x_and_y, ls, rs, conjecture, negated_conjecture;
    Z3_ast args[2];

    printf("\nDeMorgan\n");
    
    cfg                = Z3_mk_config();
    ctx                = Z3_mk_context(cfg);
    Z3_del_config(cfg);
#ifdef TRACING
    Z3_trace_to_stderr(ctx);
#endif
    bool_type          = Z3_mk_bool_type(ctx);
    symbol_x           = Z3_mk_int_symbol(ctx, 0);
    symbol_y           = Z3_mk_int_symbol(ctx, 1);
    x                  = Z3_mk_const(ctx, symbol_x, bool_type);
    y                  = Z3_mk_const(ctx, symbol_y, bool_type);
    
    /* De Morgan - with a negation around */
    /* !(!(x && y) <-> (!x || !y)) */
    not_x              = Z3_mk_not(ctx, x);
    not_y              = Z3_mk_not(ctx, y);
    args[0]            = x;
    args[1]            = y;
    x_and_y            = Z3_mk_and(ctx, 2, args);
    ls                 = Z3_mk_not(ctx, x_and_y);
    args[0]            = not_x;
    args[1]            = not_y;
    rs                 = Z3_mk_or(ctx, 2, args);
    conjecture         = Z3_mk_iff(ctx, ls, rs);
    negated_conjecture = Z3_mk_not(ctx, conjecture);
    
    Z3_assert_cnstr(ctx, negated_conjecture);
    switch (Z3_check(ctx)) {
    case Z3_L_FALSE:
        /* The negated conjecture was unsatisfiable, hence the conjecture is valid */
        printf("DeMorgan is valid\n");
        break;
    case Z3_L_UNDEF:
        /* Check returned undef */
        printf("Undef\n");
        break;
    case Z3_L_TRUE:
        /* The negated conjecture was satisfiable, hence the conjecture is not valid */
        printf("DeMorgan is not valid\n");
        break;
    }
    Z3_del_context(ctx);
}

/**
   \brief Find a model for <tt>x xor y</tt>.
*/
void find_model_example1() 
{
    Z3_context ctx;
    Z3_ast x, y, x_xor_y;

    printf("\nfind_model_example1\n");

    ctx     = mk_context();

    x       = mk_bool_var(ctx, "x");
    y       = mk_bool_var(ctx, "y");
    x_xor_y = Z3_mk_xor(ctx, x, y);
    
    Z3_assert_cnstr(ctx, x_xor_y);

    printf("model for: x xor y\n");
    check(ctx, Z3_L_TRUE);

    Z3_del_context(ctx);
}

/**
   \brief Find a model for <tt>x < y + 1, x > 2</tt>.
   Then, assert <tt>not(x = y)</tt>, and find another model.
*/
void find_model_example2() 
{
    Z3_context ctx;
    Z3_ast x, y, one, two, y_plus_one;
    Z3_ast x_eq_y;
    Z3_ast args[2];
    Z3_ast c1, c2, c3;

    printf("\nfind_model_example2\n");
    
    ctx        = mk_context();
    x          = mk_int_var(ctx, "x");
    y          = mk_int_var(ctx, "y");
    one        = mk_int(ctx, 1);
    two        = mk_int(ctx, 2);

    args[0]    = y;
    args[1]    = one;
    y_plus_one = Z3_mk_add(ctx, 2, args);

    c1         = Z3_mk_lt(ctx, x, y_plus_one);
    c2         = Z3_mk_gt(ctx, x, two);
    
    Z3_assert_cnstr(ctx, c1);
    Z3_assert_cnstr(ctx, c2);

    printf("model for: x < y + 1, x > 2\n");
    check(ctx, Z3_L_TRUE);

    /* assert not(x = y) */
    x_eq_y     = Z3_mk_eq(ctx, x, y);
    c3         = Z3_mk_not(ctx, x_eq_y);
    Z3_assert_cnstr(ctx, c3);

    printf("model for: x < y + 1, x > 2, not(x = y)\n");
    check(ctx, Z3_L_TRUE);

    Z3_del_context(ctx);
}

/**
   \brief Prove <tt>x = y implies g(x) = g(y)</tt>, and
   disprove <tt>x = y implies g(g(x)) = g(y)</tt>.

   This function demonstrates how to create uninterpreted types and
   functions.
*/
void prove_example1() 
{
    Z3_context ctx;
    Z3_symbol U_name, g_name, x_name, y_name;
    Z3_type_ast U;
    Z3_type_ast g_domain[1];
    Z3_const_decl_ast g;
    Z3_ast x, y, gx, ggx, gy;
    Z3_ast eq, f;

    printf("\nprove_example1\n");
    
    ctx        = mk_context();
    
    /* create uninterpreted type. */
    U_name     = Z3_mk_string_symbol(ctx, "U");
    U          = Z3_mk_uninterpreted_type(ctx, U_name);
    
    /* declare function g */
    g_name      = Z3_mk_string_symbol(ctx, "g");
    g_domain[0] = U;
    g           = Z3_mk_func_decl(ctx, g_name, 1, g_domain, U);

    /* create x and y */
    x_name      = Z3_mk_string_symbol(ctx, "x");
    y_name      = Z3_mk_string_symbol(ctx, "y");
    x           = Z3_mk_const(ctx, x_name, U);
    y           = Z3_mk_const(ctx, y_name, U);
    /* create g(x), g(y) */
    gx          = mk_unary_app(ctx, g, x);
    gy          = mk_unary_app(ctx, g, y);
    
    /* assert x = y */
    eq          = Z3_mk_eq(ctx, x, y);
    Z3_assert_cnstr(ctx, eq);

    /* prove g(x) = g(y) */
    f           = Z3_mk_eq(ctx, gx, gy);
    printf("prove: x = y implies g(x) = g(y)\n");
    prove(ctx, f, Z3_TRUE);

    /* create g(g(x)) */
    ggx         = mk_unary_app(ctx, g, gx);
    
    /* disprove g(g(x)) = g(y) */
    f           = Z3_mk_eq(ctx, ggx, gy);
    printf("disprove: x = y implies g(g(x)) = g(y)\n");
    prove(ctx, f, Z3_FALSE);

    Z3_del_context(ctx);
}

/**
   \brief Prove <tt>not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0 </tt>.
   Then, show that <tt>z < -1</tt> is not implied.

   This example demonstrates how to combine uninterpreted functions and arithmetic.
*/
void prove_example2() 
{
    Z3_context ctx;
    Z3_type_ast int_type;
    Z3_symbol g_name;
    Z3_type_ast g_domain[1];
    Z3_const_decl_ast g;
    Z3_ast x, y, z, zero, minus_one, x_plus_z, gx, gy, gz, gx_gy, ggx_gy;
    Z3_ast args[2];
    Z3_ast eq, c1, c2, c3, f;

    printf("\nprove_example2\n");
    
    ctx        = mk_context();

    /* declare function g */
    int_type    = Z3_mk_int_type(ctx);
    g_name      = Z3_mk_string_symbol(ctx, "g");
    g_domain[0] = int_type;
    g           = Z3_mk_func_decl(ctx, g_name, 1, g_domain, int_type);
    
    /* create x, y, and z */
    x           = mk_int_var(ctx, "x");
    y           = mk_int_var(ctx, "y");
    z           = mk_int_var(ctx, "z");

    /* create gx, gy, gz */
    gx          = mk_unary_app(ctx, g, x);
    gy          = mk_unary_app(ctx, g, y);
    gz          = mk_unary_app(ctx, g, z);
    
    /* create zero */
    zero        = mk_int(ctx, 0);

    /* assert not(g(g(x) - g(y)) = g(z)) */
    args[0]     = gx;
    args[1]     = gy;
    gx_gy       = Z3_mk_sub(ctx, 2, args);
    ggx_gy      = mk_unary_app(ctx, g, gx_gy);
    eq          = Z3_mk_eq(ctx, ggx_gy, gz);
    c1          = Z3_mk_not(ctx, eq);
    Z3_assert_cnstr(ctx, c1);

    /* assert x + z <= y */
    args[0]     = x;
    args[1]     = z;
    x_plus_z    = Z3_mk_add(ctx, 2, args);
    c2          = Z3_mk_le(ctx, x_plus_z, y);
    Z3_assert_cnstr(ctx, c2);

    /* assert y <= x */
    c3          = Z3_mk_le(ctx, y, x);
    Z3_assert_cnstr(ctx, c3);

    /* prove z < 0 */
    f           = Z3_mk_lt(ctx, z, zero);
    printf("prove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0\n");
    prove(ctx, f, Z3_TRUE);

    /* disprove z < -1 */
    minus_one   = mk_int(ctx, -1);
    f           = Z3_mk_lt(ctx, z, minus_one);
    printf("disprove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < -1\n");
    prove(ctx, f, Z3_FALSE);

    Z3_del_context(ctx);
}

/**
   \brief Show how push & pop can be used to create "backtracking"
   points.

   This example also demonstrates how big numbers can be created in Z3.
*/
void push_pop_example1() 
{
    Z3_context ctx;
    Z3_type_ast int_type;
    Z3_symbol x_sym, y_sym;
    Z3_ast x, y, big_number, three;
    Z3_ast c1, c2, c3;

    printf("\npush_pop_example1\n");

    ctx        = mk_context();

    /* create a big number */
    int_type   = Z3_mk_int_type(ctx);
    big_number = Z3_mk_numeral(ctx, "1000000000000000000000000000000000000000000000000000000", int_type);
    
    /* create number 3 */
    three      = Z3_mk_numeral(ctx, "3", int_type);

    /* create x */
    x_sym      = Z3_mk_string_symbol(ctx, "x");
    x          = Z3_mk_const(ctx, x_sym, int_type);

    /* assert x >= "big number" */
    c1         = Z3_mk_ge(ctx, x, big_number);
    printf("assert: x >= 'big number'\n");
    Z3_assert_cnstr(ctx, c1);

    /* create a backtracking point */
    printf("push\n");
    Z3_push(ctx);

    /* assert x <= 3 */
    c2         = Z3_mk_le(ctx, x, three);
    printf("assert: x <= 3\n");
    Z3_assert_cnstr(ctx, c2);

    /* context is inconsistent at this point */
    check2(ctx, Z3_L_FALSE);

    /* backtrack: the constraint x <= 3 will be removed, since it was
       asserted after the last Z3_push. */
    printf("pop\n");
    Z3_pop(ctx, 1);

    /* the context is consistent again. */
    check2(ctx, Z3_L_TRUE);

    /* new constraints can be asserted... */
    
    /* create y */
    y_sym      = Z3_mk_string_symbol(ctx, "y");
    y          = Z3_mk_const(ctx, y_sym, int_type);

    /* assert y > x */
    c3         = Z3_mk_gt(ctx, y, x);
    printf("assert: y > x\n");
    Z3_assert_cnstr(ctx, c3);

    /* the context is still consistent. */
    check2(ctx, Z3_L_TRUE);
    
    Z3_del_context(ctx);
}

/**
   \brief Prove that <tt>f(x, y) = f(w, v) implies y = v</tt> when 
   \c f is injective in the second argument.

   \sa assert_inj_axiom.
*/
void quantifier_example1() 
{
    Z3_config  cfg;
    Z3_context ctx;
    Z3_type_ast       int_type;
    Z3_symbol         f_name;
    Z3_type_ast       f_domain[2];
    Z3_const_decl_ast f;
    Z3_ast            x, y, w, v, fxy, fwv;
    Z3_ast            p1, p2, p3, not_p3;

    printf("\nquantifier_example1\n");

    cfg = Z3_mk_config();
    /* If quantified formulas are asserted in a logical context, then
       the model produced by Z3 should be viewed as a potential model.

       The option PARTIAL_MODELS=true will allow Z3 to create partial
       function interpretations, that is, the "else" part is
       unspecified.
    */
    Z3_set_param_value(cfg, "PARTIAL_MODELS", "true");
    ctx = mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);

    /* declare function f */
    int_type    = Z3_mk_int_type(ctx);
    f_name      = Z3_mk_string_symbol(ctx, "f");
    f_domain[0] = int_type;
    f_domain[1] = int_type;
    f           = Z3_mk_func_decl(ctx, f_name, 2, f_domain, int_type);
  
    /* assert that f is injective in the second argument. */
    assert_inj_axiom(ctx, f, 1);
    
    /* create x, y, v, w, fxy, fwv */
    x           = mk_int_var(ctx, "x");
    y           = mk_int_var(ctx, "y");
    v           = mk_int_var(ctx, "v");
    w           = mk_int_var(ctx, "w");
    fxy         = mk_binary_app(ctx, f, x, y);
    fwv         = mk_binary_app(ctx, f, w, v);
    
    /* assert f(x, y) = f(w, v) */
    p1          = Z3_mk_eq(ctx, fxy, fwv);
    Z3_assert_cnstr(ctx, p1);

    /* prove f(x, y) = f(w, v) implies y = v */
    p2          = Z3_mk_eq(ctx, y, v);
    printf("prove: f(x, y) = f(w, v) implies y = v\n");
    prove(ctx, p2, Z3_TRUE);

    /* disprove f(x, y) = f(w, v) implies x = w */
    /* using check2 instead of prove */
    p3          = Z3_mk_eq(ctx, x, w);
    not_p3      = Z3_mk_not(ctx, p3);
    Z3_assert_cnstr(ctx, not_p3);
    printf("disprove: f(x, y) = f(w, v) implies x = w\n");
    printf("that is: not(f(x, y) = f(w, v) implies x = w) is satisfiable\n");
    check2(ctx, Z3_L_TRUE);

    Z3_del_context(ctx);
}

/**
   \brief Prove <tt>store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))</tt>.
   
   This example demonstrates how to use the array theory.
*/
void array_example1() 
{
    Z3_context ctx;
    Z3_type_ast int_type, array_type;
    Z3_ast a1, a2, i1, v1, i2, v2, i3;
    Z3_ast st1, st2, sel1, sel2;
    Z3_ast antecedent, consequent;
    Z3_ast ds[3];
    Z3_ast thm;

    printf("\narray_example1\n");

    ctx = mk_context();

    int_type    = Z3_mk_int_type(ctx);
    array_type  = Z3_mk_array_type(ctx, int_type, int_type);

    a1          = mk_var(ctx, "a1", array_type);
    a2          = mk_var(ctx, "a2", array_type);
    i1          = mk_var(ctx, "i1", int_type);
    i2          = mk_var(ctx, "i2", int_type);
    i3          = mk_var(ctx, "i3", int_type);
    v1          = mk_var(ctx, "v1", int_type);
    v2          = mk_var(ctx, "v2", int_type);
    
    st1         = Z3_mk_store(ctx, a1, i1, v1);
    st2         = Z3_mk_store(ctx, a2, i2, v2);
    
    sel1        = Z3_mk_select(ctx, a1, i3);
    sel2        = Z3_mk_select(ctx, a2, i3);

    /* create antecedent */
    antecedent  = Z3_mk_eq(ctx, st1, st2);

    /* create consequent: i1 = i3 or  i2 = i3 or select(a1, i3) = select(a2, i3) */
    ds[0]       = Z3_mk_eq(ctx, i1, i3);
    ds[1]       = Z3_mk_eq(ctx, i2, i3);
    ds[2]       = Z3_mk_eq(ctx, sel1, sel2);
    consequent  = Z3_mk_or(ctx, 3, ds);

    /* prove store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3)) */
    thm         = Z3_mk_implies(ctx, antecedent, consequent);
    printf("prove: store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))\n");
    printf("%s\n", Z3_ast_to_string(ctx, thm));
    prove(ctx, thm, Z3_TRUE);

    Z3_del_context(ctx);
}

/**
   \brief Show that <tt>distinct(a_0, ... , a_n)</tt> is
   unsatisfiable when \c a_i's are arrays from boolean to
   boolean and n > 4.

   This example also shows how to use the \c distinct construct.
*/
void array_example2() 
{
    Z3_context ctx;
    Z3_type_ast bool_type, array_type;
    Z3_ast      a[5];
    Z3_ast      d;
    unsigned      i, n;

    printf("\narray_example2\n");

    for (n = 2; n <= 5; n++) {
        printf("n = %d\n", n);
        ctx = mk_context();
        
        bool_type   = Z3_mk_bool_type(ctx);
        array_type  = Z3_mk_array_type(ctx, bool_type, bool_type);
        
        /* create arrays */
        for (i = 0; i < n; i++) {
            Z3_symbol s = Z3_mk_int_symbol(ctx, i);
            a[i]          = Z3_mk_const(ctx, s, array_type);
        }
        
        /* assert distinct(a[0], ..., a[n]) */
        d = Z3_mk_distinct(ctx, n, a);
        printf("%s\n", Z3_ast_to_string(ctx, d));
        Z3_assert_cnstr(ctx, d);

        /* context is satisfiable if n < 5 */
        check2(ctx, n < 5 ? Z3_L_TRUE : Z3_L_FALSE);
        
        Z3_del_context(ctx);
    }
}

/**
   \brief Simple array type construction/deconstruction example.
*/
void array_example3() 
{
    Z3_context ctx;
    Z3_type_ast bool_type, int_type, array_type;
    Z3_type_ast domain, range;
    printf("\narray_example3\n");

    ctx      = mk_context();

    bool_type  = Z3_mk_bool_type(ctx);
    int_type   = Z3_mk_int_type(ctx); 
    array_type = Z3_mk_array_type(ctx, int_type, bool_type);

    if (Z3_get_type_kind(ctx, array_type) != Z3_ARRAY_TYPE) {
        exitf("type must be an array type");
    }
    
    domain = Z3_get_array_type_domain(ctx, array_type);
    range  = Z3_get_array_type_range(ctx, array_type);

    printf("domain: ");
    display_type(ctx, stdout, domain);
    printf("\n");
    printf("range:  ");
    display_type(ctx, stdout, range);
    printf("\n");

    if (!Z3_is_eq(ctx, Z3_type_ast_to_ast(ctx, int_type),  Z3_type_ast_to_ast(ctx, domain)) ||
        !Z3_is_eq(ctx, Z3_type_ast_to_ast(ctx, bool_type), Z3_type_ast_to_ast(ctx, range))) {
        exitf("invalid array type");
    }

    Z3_del_context(ctx);
}

/**
   \brief Simple tuple type example. It creates a tuple that is a pair of real numbers.
*/
void tuple_example1() 
{
    Z3_context         ctx;
    Z3_type_ast        real_type, pair_type;
    Z3_symbol          mk_tuple_name;
    Z3_const_decl_ast  mk_tuple_decl;
    Z3_symbol          proj_names[2]; 
    Z3_type_ast        proj_types[2]; 
    Z3_const_decl_ast  proj_decls[2];
    Z3_const_decl_ast  get_x_decl, get_y_decl;

    printf("\ntuple_example1\n");
    
    ctx       = mk_context();

    real_type = Z3_mk_real_type(ctx);

    /* Create pair (tuple) type */
    mk_tuple_name = Z3_mk_string_symbol(ctx, "mk_pair");
    proj_names[0] = Z3_mk_string_symbol(ctx, "get_x");
    proj_names[1] = Z3_mk_string_symbol(ctx, "get_y");
    proj_types[0] = real_type;
    proj_types[1] = real_type;
    /* Z3_mk_tuple_type will set mk_tuple_decl and proj_decls */
    pair_type     = Z3_mk_tuple_type(ctx, mk_tuple_name, 2, proj_names, proj_types, &mk_tuple_decl, proj_decls);
    get_x_decl    = proj_decls[0]; /* function that extracts the first element of a tuple. */
    get_y_decl    = proj_decls[1]; /* function that extracts the second element of a tuple. */
    
    printf("tuple_type: ");
    display_type(ctx, stdout, pair_type);
    printf("\n");

    {
        /* prove that get_x(mk_pair(x,y)) == 1 implies x = 1*/
        Z3_ast app1, app2, x, y, one;
        Z3_ast eq1, eq2, eq3, thm;
        
        x    = mk_real_var(ctx, "x");
        y    = mk_real_var(ctx, "y");
        app1 = mk_binary_app(ctx, mk_tuple_decl, x, y);
        app2 = mk_unary_app(ctx, get_x_decl, app1); 
        one  = Z3_mk_numeral(ctx, "1", real_type);
        eq1  = Z3_mk_eq(ctx, app2, one);
        eq2  = Z3_mk_eq(ctx, x, one);
        thm  = Z3_mk_implies(ctx, eq1, eq2);
        printf("prove: get_x(mk_pair(x, y)) = 1 implies x = 1\n");
        prove(ctx, thm, Z3_TRUE);

        /* disprove that get_x(mk_pair(x,y)) == 1 implies y = 1*/
        eq3  = Z3_mk_eq(ctx, y, one);
        thm  = Z3_mk_implies(ctx, eq1, eq3);
        printf("disprove: get_x(mk_pair(x, y)) = 1 implies y = 1\n");
        prove(ctx, thm, Z3_FALSE);
    }

    {
        /* prove that get_x(p1) = get_x(p2) and get_y(p1) = get_y(p2) implies p1 = p2 */
        Z3_ast p1, p2, x1, x2, y1, y2;
        Z3_ast antecedents[2];
        Z3_ast antecedent, consequent, thm;
        
        p1             = mk_var(ctx, "p1", pair_type);
        p2             = mk_var(ctx, "p2", pair_type);
        x1             = mk_unary_app(ctx, get_x_decl, p1);
        y1             = mk_unary_app(ctx, get_y_decl, p1);
        x2             = mk_unary_app(ctx, get_x_decl, p2);
        y2             = mk_unary_app(ctx, get_y_decl, p2);
        antecedents[0] = Z3_mk_eq(ctx, x1, x2);
        antecedents[1] = Z3_mk_eq(ctx, y1, y2);
        antecedent     = Z3_mk_and(ctx, 2, antecedents);
        consequent     = Z3_mk_eq(ctx, p1, p2);
        thm            = Z3_mk_implies(ctx, antecedent, consequent);
        printf("prove: get_x(p1) = get_x(p2) and get_y(p1) = get_y(p2) implies p1 = p2\n");
        prove(ctx, thm, Z3_TRUE);

        /* disprove that get_x(p1) = get_x(p2) implies p1 = p2 */
        thm            = Z3_mk_implies(ctx, antecedents[0], consequent);
        printf("disprove: get_x(p1) = get_x(p2) implies p1 = p2\n");
        prove(ctx, thm, Z3_FALSE);
    }

    {
        /* demonstrate how to use the mk_tuple_update function */
        /* prove that p2 = update(p1, 0, 10) implies get_x(p2) = 10 */
        Z3_ast p1, p2, one, ten, updt, x, y;
        Z3_ast antecedent, consequent, thm;

        p1             = mk_var(ctx, "p1", pair_type);
        p2             = mk_var(ctx, "p2", pair_type);
        one            = Z3_mk_numeral(ctx, "1", real_type);
        ten            = Z3_mk_numeral(ctx, "10", real_type);
        updt           = mk_tuple_update(ctx, p1, 0, ten);
        antecedent     = Z3_mk_eq(ctx, p2, updt);
        x              = mk_unary_app(ctx, get_x_decl, p2);
        consequent     = Z3_mk_eq(ctx, x, ten);
        thm            = Z3_mk_implies(ctx, antecedent, consequent);
        printf("prove: p2 = update(p1, 0, 10) implies get_x(p2) = 10\n");
        prove(ctx, thm, Z3_TRUE);

        /* disprove that p2 = update(p1, 0, 10) implies get_y(p2) = 10 */
        y              = mk_unary_app(ctx, get_y_decl, p2);
        consequent     = Z3_mk_eq(ctx, y, ten);
        thm            = Z3_mk_implies(ctx, antecedent, consequent);
        printf("disprove: p2 = update(p1, 0, 10) implies get_y(p2) = 10\n");
        prove(ctx, thm, Z3_FALSE);
    }

    Z3_del_context(ctx);
}

/**
   \brief Simple bit-vector example. This example disproves that x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers
*/
void bitvector_example1() 
{
    Z3_context         ctx;
    Z3_type_ast        bv_type;
    Z3_ast             x, zero, ten, x_minus_ten, c1, c2, thm;

    printf("\nbitvector_example1\n");
    
    ctx       = mk_context();
    
    bv_type   = Z3_mk_bv_type(ctx, 32);
    
    x           = mk_var(ctx, "x", bv_type);
    zero        = Z3_mk_numeral(ctx, "0", bv_type);
    ten         = Z3_mk_numeral(ctx, "10", bv_type);
    x_minus_ten = Z3_mk_bvsub(ctx, x, ten);
    /* bvsle is signed less than or equal to */
    c1          = Z3_mk_bvsle(ctx, x, ten);
    c2          = Z3_mk_bvsle(ctx, x_minus_ten, zero);
    thm         = Z3_mk_iff(ctx, c1, c2);
    printf("disprove: x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers\n");
    prove(ctx, thm, Z3_FALSE);
    
    Z3_del_context(ctx);
}

/**
   \brief Find x and y such that: x ^ y - 103 == x * y
*/
void bitvector_example2()
{
    Z3_context ctx = mk_context();
 
    /* construct x ^ y - 103 == x * y */
    Z3_type_ast bv_type = Z3_mk_bv_type(ctx, 32);
    Z3_ast x = mk_var(ctx, "x", bv_type);
    Z3_ast y = mk_var(ctx, "y", bv_type);
    Z3_ast x_xor_y = Z3_mk_bvxor(ctx, x, y);
    Z3_ast c103 = Z3_mk_numeral(ctx, "103", bv_type);
    Z3_ast lhs = Z3_mk_bvsub(ctx, x_xor_y, c103);
    Z3_ast rhs = Z3_mk_bvmul(ctx, x, y);
    Z3_ast ctr = Z3_mk_eq(ctx, lhs, rhs);

    printf("\nbitvector_example2\n");
    printf("find values of x and y, such that x ^ y - 103 == x * y\n");
    
    /* add the constraint <tt>x ^ y - 103 == x * y<\tt> to the logical context */
    Z3_assert_cnstr(ctx, ctr);
    
    /* find a model (i.e., values for x an y that satisfy the constraint */
    check(ctx, Z3_L_TRUE);
    
    Z3_del_context(ctx);
}

/**
   \brief Demonstrate how to use #Z3_eval.
*/
void eval_example1() 
{
    Z3_context ctx;
    Z3_ast x, y, two;
    Z3_ast c1, c2;
    Z3_model m;

    printf("\neval_example1\n");
    
    ctx        = mk_context();
    x          = mk_int_var(ctx, "x");
    y          = mk_int_var(ctx, "y");
    two        = mk_int(ctx, 2);
    
    /* assert x < y */
    c1         = Z3_mk_lt(ctx, x, y);
    Z3_assert_cnstr(ctx, c1);

    /* assert x > 2 */
    c2         = Z3_mk_gt(ctx, x, two);
    Z3_assert_cnstr(ctx, c2);

    /* find model for the constraints above */
    if (Z3_check_and_get_model(ctx, &m) == Z3_L_TRUE) {
        Z3_ast   x_plus_y;
        Z3_ast   args[2] = {x, y};
        Z3_value v;
        printf("MODEL:\n%s", Z3_model_to_string(ctx, m));
        x_plus_y = Z3_mk_add(ctx, 2, args);
        printf("\nevaluating x+y\n");
        if (Z3_eval(ctx, m, x_plus_y, &v)) {
            printf("result = ");
            display_value(ctx, stdout, v);
            printf("\n");
        }
        else {
            exitf("failed to evaluate: x+y");
        }
        Z3_del_model(m);
    }
    else {
        exitf("the constraints are satisfiable");
    }

    Z3_del_context(ctx);
}

/**
   \brief Several logical context can be used simultaneously.
*/
void two_contexts_example1() 
{
    Z3_context ctx1, ctx2;
    Z3_ast x1, x2;

    printf("\ntwo_contexts_example1\n");
    
    /* using the same (default) configuration to initialized both logical contexts. */
    ctx1 = mk_context();
    ctx2 = mk_context();
    
    x1 = Z3_mk_const(ctx1, Z3_mk_int_symbol(ctx1,0), Z3_mk_bool_type(ctx1));
    x2 = Z3_mk_const(ctx2, Z3_mk_int_symbol(ctx2,0), Z3_mk_bool_type(ctx2));

    Z3_del_context(ctx1);
    
    /* ctx2 can still be used. */
    printf("%s\n", Z3_ast_to_string(ctx2, x2));
    
    Z3_del_context(ctx2);
}

/**
   \brief Demonstrates how error codes can be read insted of registering an error handler.
 */
void error_code_example1() 
{
    Z3_config cfg;
    Z3_context ctx;
    Z3_ast x;
    Z3_model m;
    Z3_value v;
    Z3_const_decl_ast x_decl;
    const char * str;

    printf("\nerror_code_example1\n");
    
    /* Do not register an error handler, as we want to use Z3_get_error_code manually */
    cfg = Z3_mk_config();
    ctx = mk_context_custom(cfg, NULL);
    Z3_del_config(cfg);

    x          = mk_bool_var(ctx, "x");
    x_decl     = Z3_get_const_ast_decl(ctx, Z3_to_const_ast(ctx, x));
    Z3_assert_cnstr(ctx, x);
    
    if (Z3_check_and_get_model(ctx, &m) != Z3_L_TRUE) {
        exitf("unexpected result");
    }

    v = Z3_get_value(ctx, m, x_decl);
    if (Z3_get_error_code(ctx) == Z3_OK) {
        printf("last call succeeded.\n");
    }
    /* The following call will fail since the value of x is a boolean */
    str = Z3_get_numeral_value_string(ctx, v);
    if (Z3_get_error_code(ctx) != Z3_OK) {
        printf("last call failed.\n");
    }
    Z3_del_model(m);
    Z3_del_context(ctx);
}

/**
   \brief Demonstrates how error handlers can be used.
*/
void error_code_example2() 
{
    Z3_config cfg;
    Z3_context ctx = NULL;
    int r;

    printf("\nerror_code_example2\n");
    
    /* low tech try&catch */
    r = setjmp(g_catch_buffer);
    if (r == 0) {
        Z3_ast x, y, app;
        
        cfg = Z3_mk_config();
        ctx = mk_context_custom(cfg, throw_z3_error);
        Z3_del_config(cfg);
        
        x   = mk_int_var(ctx, "x");
        y   = mk_bool_var(ctx, "y");
        printf("before Z3_mk_iff\n"); 
        /* the next call will produce an error */
        app = Z3_mk_iff(ctx, x, y);
        unreachable();
        Z3_del_context(ctx);
    }
    else {
        printf("Z3 error: %s.\n", Z3_get_error_msg(r));
        if (cfg != NULL) {
            Z3_del_context(ctx);
        }
    }
}

/**
   \brief Demonstrates how to use the SMTLIB parser.
 */
void parser_example1() 
{
    Z3_context ctx;
    unsigned i, num_formulas;

    printf("\nparser_example1\n");
    
    ctx        = mk_context();

    /* arithmetic theory is automatically initialized, when an
       int/real variable or arith operation is created using the API.
       Since no such function is invoked in this example, we should do
       that manually.
    */
    Z3_enable_arithmetic(ctx);
   
    Z3_parse_smtlib_string(ctx, 
                           "(benchmark tst :extrafuns ((x Int) (y Int)) :formula (> x y) :formula (> x 0))",
                           0, 0, 0,
                           0, 0, 0);
    num_formulas = Z3_get_smtlib_num_formulas(ctx);
    for (i = 0; i < num_formulas; i++) {
        Z3_ast f = Z3_get_smtlib_formula(ctx, i);
        printf("formula %d: %s\n", i, Z3_ast_to_string(ctx, f));
        Z3_assert_cnstr(ctx, f);
    }
    
    check(ctx, Z3_L_TRUE);

    Z3_del_context(ctx);
}

/**
   \brief Demonstrates how to initialize the parser symbol table.
 */
void parser_example2() 
{
    Z3_context ctx;
    Z3_ast x, y;
    Z3_symbol         names[2];
    Z3_const_decl_ast decls[2];
    Z3_ast f;

    printf("\nparser_example2\n");

    ctx        = mk_context();

    /* Z3_enable_arithmetic doesn't need to be invoked in this example
       because it will be implicitly invoked by mk_int_var.
    */
    
    x        = mk_int_var(ctx, "x");
    decls[0] = Z3_get_const_ast_decl(ctx, Z3_to_const_ast(ctx, x));
    y        = mk_int_var(ctx, "y");
    decls[1] = Z3_get_const_ast_decl(ctx, Z3_to_const_ast(ctx, y));
    
    names[0] = Z3_mk_string_symbol(ctx, "a");
    names[1] = Z3_mk_string_symbol(ctx, "b");
    
    Z3_parse_smtlib_string(ctx, 
                           "(benchmark tst :formula (> a b))",
                           0, 0, 0,
                           /* 'x' and 'y' declarations are inserted as 'a' and 'b' into the parser symbol table. */
                           2, names, decls);
    f = Z3_get_smtlib_formula(ctx, 0);
    printf("formula: %s\n", Z3_ast_to_string(ctx, f));
    Z3_assert_cnstr(ctx, f);
    check(ctx, Z3_L_TRUE);

    Z3_del_context(ctx);
}

/**
   \brief Demonstrates how to initialize the parser symbol table.
 */
void parser_example3() 
{
    Z3_config  cfg;
    Z3_context ctx;
    Z3_type_ast       int_type;
    Z3_symbol         g_name;
    Z3_type_ast       g_domain[2];
    Z3_const_decl_ast g;
    Z3_ast            thm;

    printf("\nparser_example3\n");

    cfg = Z3_mk_config();
    /* See quantifer_example1 */
    Z3_set_param_value(cfg, "PARTIAL_MODELS", "true");
    ctx = mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);

    /* declare function g */
    int_type    = Z3_mk_int_type(ctx);
    g_name      = Z3_mk_string_symbol(ctx, "g");
    g_domain[0] = int_type;
    g_domain[1] = int_type;
    g           = Z3_mk_func_decl(ctx, g_name, 2, g_domain, int_type);
    
    assert_comm_axiom(ctx, g);

    Z3_parse_smtlib_string(ctx, 
                           "(benchmark tst :formula (forall (x Int) (y Int) (implies (= x y) (= (g x 0) (g 0 y)))))",
                           0, 0, 0,
                           1, &g_name, &g);
    thm = Z3_get_smtlib_formula(ctx, 0);
    printf("formula: %s\n", Z3_ast_to_string(ctx, thm));
    prove(ctx, thm, Z3_TRUE);

    Z3_del_context(ctx);
}

/**
   \brief Display the declarations, assumptions and formulas in a SMT-LIB string.
*/
void parser_example4() 
{
    Z3_context ctx;
    unsigned i, num_decls, num_assumptions, num_formulas;

    printf("\nparser_example4\n");
    
    ctx        = mk_context();

    /* arithmetic theory is automatically initialized, when an
       int/real variable or arith operation is created using the API.
       Since no such function is invoked in this example, we should do
       that manually.
    */
    Z3_enable_arithmetic(ctx);
    
    Z3_parse_smtlib_string(ctx, 
                           "(benchmark tst :extrafuns ((x Int) (y Int)) :assumption (= x 20) :formula (> x y) :formula (> x 0))",
                           0, 0, 0,
                           0, 0, 0);
    num_decls = Z3_get_smtlib_num_decls(ctx);
    for (i = 0; i < num_decls; i++) {
        Z3_const_decl_ast d = Z3_get_smtlib_decl(ctx, i);
        printf("declaration %d: %s\n", i, Z3_ast_to_string(ctx, Z3_const_decl_ast_to_ast(ctx, d)));
    }
    num_assumptions = Z3_get_smtlib_num_assumptions(ctx);
    for (i = 0; i < num_assumptions; i++) {
        Z3_ast a = Z3_get_smtlib_assumption(ctx, i);
        printf("assumption %d: %s\n", i, Z3_ast_to_string(ctx, a));
    }
    num_formulas = Z3_get_smtlib_num_formulas(ctx);
    for (i = 0; i < num_formulas; i++) {
        Z3_ast f = Z3_get_smtlib_formula(ctx, i);
        printf("formula %d: %s\n", i, Z3_ast_to_string(ctx, f));
    }
    Z3_del_context(ctx);
}

/**
   \brief Demonstrates how to handle parser errors using Z3 error handling support.
*/
void parser_example5() 
{
    Z3_config  cfg;
    Z3_context ctx = NULL;
    int r;

    printf("\nparser_example5\n");

    r = setjmp(g_catch_buffer);
    if (r == 0) {
        cfg = Z3_mk_config();
        ctx = mk_context_custom(cfg, throw_z3_error);
        Z3_del_config(cfg);
        
        Z3_enable_arithmetic(ctx);
        
        Z3_parse_smtlib_string(ctx, 
                               /* the following string has a parsing error: missing parenthesis */
                               "(benchmark tst :extrafuns ((x Int (y Int)) :formula (> x y) :formula (> x 0))",
                               0, 0, 0,
                               0, 0, 0);
        unreachable();
        Z3_del_context(ctx);
    }
    else {
        printf("Z3 error: %s.\n", Z3_get_error_msg(r));
        if (ctx != NULL) {
            Z3_del_context(ctx);
        }
    }
}

/**
   \brief Test ite-term (if-then-else terms).
*/
void ite_example() 
{
    Z3_context ctx;
    Z3_ast f, one, zero, ite;
    
    printf("\nite_example\n");
 
    ctx = mk_context();
    
    f    = Z3_mk_false(ctx);
    one  = mk_int(ctx, 1);
    zero = mk_int(ctx, 0);
    ite  = Z3_mk_ite(ctx, f, one, zero);
    
    printf("term: %s\n", Z3_ast_to_string(ctx, ite));

    /* delete logical context */
    Z3_del_context(ctx);
}

/**
   \brief Simplifier example.
*/
void simplifier_example() {
    Z3_context ctx;
    Z3_ast x, y, z, u, t1, t2;
	Z3_ast args[2] = { 0, 0 };
    printf("\nsimplifier_example\n");

    ctx = mk_context();
    x = mk_int_var(ctx,"x");
    y = mk_int_var(ctx,"y");
    z = mk_int_var(ctx,"z");
    u = mk_int_var(ctx,"u");
    
    args[0] = x;
    args[1] = z;
    t1 = Z3_mk_add(ctx, 2, args);
    args[0] = y;
    args[1] = t1;
    t1 = Z3_mk_sub(ctx, 2, args);
    args[0] = x;
    args[1] = t1;
    t1 = Z3_mk_add(ctx, 2, args);
    t2 = Z3_simplify(ctx, t1);
    printf("%s -> ", Z3_ast_to_string(ctx, t1));
    printf("%s\n", Z3_ast_to_string(ctx,t2));
    Z3_del_context(ctx);
}

typedef struct bound_list {
    struct bound_list* m_next;
    unsigned     m_num_bound;
    Z3_ast      m_quantifier;
};

void print_term(Z3_context ctx, struct bound_list* bound_vars, Z3_ast t) {
    switch(Z3_get_ast_kind(ctx,t)) {
    case Z3_NUMERAL_AST: {
        printf("%s",Z3_get_numeral_ast_value(ctx,t));
        break;
    }
    case Z3_CONST_AST: {
        Z3_const_ast tc = Z3_to_const_ast(ctx,t);
        Z3_const_decl_ast f = Z3_get_const_ast_decl(ctx,tc);
        unsigned num_args = Z3_get_const_ast_num_args(ctx,tc);
        Z3_decl_kind k = Z3_get_decl_kind(ctx,f);
        unsigned i;
        printf("(");
        switch(k) {	
        case Z3_OP_ADD: printf("'+'"); break;
        case Z3_OP_MUL: printf("'*'"); break;
        case Z3_OP_SUB: printf("'-'"); break;
        default:
            printf("%s",Z3_ast_to_string(ctx,Z3_const_decl_ast_to_ast(ctx,f)));
            break;
        }
        printf(" ");
        for (i = 0; i < num_args; ++i) {
            Z3_ast arg = Z3_get_const_ast_arg(ctx,tc,i);
            print_term(ctx, bound_vars, arg);
        }
        printf(")");
        break;
    }
    case Z3_QUANTIFIER_AST: {
        struct bound_list bl;
        unsigned np = Z3_get_quantifier_num_patterns(ctx,t);
        unsigned nb = Z3_get_quantifier_num_bound(ctx,t);
        unsigned i, j;

        bl.m_next = bound_vars;
        bl.m_num_bound = nb;
        bl.m_quantifier = t;

        printf("(");
        if (Z3_is_quantifier_forall(ctx,t)) {
            printf("Forall");
        }
        else {
            printf("Exists");
        }
		printf(" ");
        for (i = 0; i < nb; ++i) {
            printf("(");
            display_symbol(ctx, stdout, Z3_get_quantifier_bound_name(ctx,t,i));
            printf(" %s) ", Z3_ast_to_string(ctx,Z3_type_ast_to_ast(ctx,Z3_get_quantifier_bound_type_ast(ctx,t,i))));
        }
		for (i = 0; i < np; ++i) {
            Z3_pattern_ast pat = Z3_get_quantifier_pattern_ast(ctx,t,i);
            unsigned nt = Z3_get_pattern_num_terms(ctx,pat);
            printf("(");
            for (j = 0; j < nt; ++j) {
                print_term(ctx, &bl, Z3_get_pattern_ast(ctx,pat,j));
                printf(" ");
            }
            printf(")");            
        }
        print_term(ctx, &bl, Z3_get_quantifier_body(ctx,t));
        printf(")");
        break;
    }
    case Z3_VAR_AST: {
        struct bound_list* bl = bound_vars;
        unsigned n = Z3_get_index_value(ctx, t);
        while (bl) {
            if (n < bl->m_num_bound) {
                display_symbol(ctx, stdout, Z3_get_quantifier_bound_name(ctx, bl->m_quantifier, bl->m_num_bound - n - 1));
                printf(" ");
                return;
            }
            else {
                n -= bl->m_num_bound;
                bl = bl->m_next;
            }
        }        
        printf("unexpected bound variable\n");
        break;
    }
    default:
        printf("unexpected case\n");
        break;
    }
}

void traverse_term_example() {
    Z3_context ctx;
    Z3_type_ast       int_type;
    Z3_symbol         f_name;
    Z3_const_decl_ast f;
    Z3_ast            x, y, fx, fy, q, body;
    Z3_pattern_ast p;
    Z3_ast fxfy[2];
    Z3_type_ast types[2];
    Z3_symbol names[2];
    ctx = mk_context();
    f_name = Z3_mk_string_symbol(ctx, "f");
    int_type = Z3_mk_int_type(ctx);
    f = Z3_mk_func_decl(ctx,f_name, 1, &int_type, int_type);
    x = Z3_mk_bound(ctx,1,int_type);
    y = Z3_mk_bound(ctx,0,int_type);
    fx = Z3_mk_app(ctx, f, 1, &x);
    fy = Z3_mk_app(ctx, f, 1, &y);
    fxfy[0] = fx;
    fxfy[1] = fy;
    p = Z3_mk_pattern(ctx, 2, fxfy);
    types[0] = int_type;
    types[1] = int_type;
    names[0] = Z3_mk_string_symbol(ctx,"x"); 
    names[1] = Z3_mk_string_symbol(ctx,"y");
    body = Z3_mk_eq(ctx,fx,Z3_mk_add(ctx, 2, fxfy));
    q = Z3_mk_forall(ctx,0,1,&p,2,types,names,body);
    printf("\ntraverse_term example\n");
    printf("%s\n",Z3_ast_to_string(ctx,q));
    print_term(ctx,0,q);
    printf("\n");
    Z3_del_context(ctx);
}


/*@}*/
/*@}*/

int main() 
{
    display_version();
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
    parser_example3();
    parser_example4();
    parser_example5();
    ite_example();
    simplifier_example();
    traverse_term_example();
    return 0;
}
