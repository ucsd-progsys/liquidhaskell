/* File generated from z3.idl */

#include <stddef.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/callback.h>
#ifdef Custom_tag
#include <caml/custom.h>
#include <caml/bigarray.h>
#endif
#include <caml/camlidlruntime.h>


#include "z3.h"

#pragma warning(disable:4090)
#ifndef __int64
#define __int64 long long
#endif
Z3_error_handler caml_z3_error_handler;
void caml_z3_error_handler(Z3_error_code e) { static char buffer[128]; char * msg = Z3_get_error_msg(e); if (strlen(msg) > 100) { failwith("Z3: error message is too big"); } else { sprintf(buffer, "Z3: %s", msg); failwith(buffer); } }
void camlidl_ml2c_z3_Z3_config(value _v1, Z3_config * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_config *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_config(Z3_config * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_config) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_config *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3_Z3_context(value _v1, Z3_context * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_context *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_context(Z3_context * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_context) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_context *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3_Z3_sort(value _v1, Z3_sort * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_sort *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_sort(Z3_sort * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_sort) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_sort *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3_Z3_func_decl(value _v1, Z3_func_decl * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_func_decl *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_func_decl(Z3_func_decl * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_func_decl) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_func_decl *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3_Z3_ast(value _v1, Z3_ast * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_ast *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_ast(Z3_ast * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_ast) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_ast *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3_Z3_app(value _v1, Z3_app * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_app *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_app(Z3_app * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_app) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_app *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3_Z3_pattern(value _v1, Z3_pattern * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_pattern *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_pattern(Z3_pattern * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_pattern) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_pattern *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3_Z3_symbol(value _v1, Z3_symbol * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_symbol *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_symbol(Z3_symbol * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_symbol) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_symbol *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3_Z3_parameter(value _v1, Z3_parameter * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_parameter *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_parameter(Z3_parameter * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_parameter) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_parameter *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3_Z3_model(value _v1, Z3_model * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_model *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_model(Z3_model * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_model) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_model *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3_Z3_literals(value _v1, Z3_literals * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_literals *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_literals(Z3_literals * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_literals) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_literals *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3_Z3_constructor(value _v1, Z3_constructor * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_constructor *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_constructor(Z3_constructor * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_constructor) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_constructor *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3_Z3_constructor_list(value _v1, Z3_constructor_list * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_constructor_list *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_constructor_list(Z3_constructor_list * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_constructor_list) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_constructor_list *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3_Z3_theory(value _v1, Z3_theory * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_theory *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_theory(Z3_theory * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_theory) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_theory *) Bp_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_z3_Z3_theory_data(value _v1, Z3_theory_data * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((Z3_theory_data *) Bp_val(_v1));
}

value camlidl_c2ml_z3_Z3_theory_data(Z3_theory_data * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(Z3_theory_data) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((Z3_theory_data *) Bp_val(_v1)) = *_c2;
  return _v1;
}

int camlidl_transl_table_z3_enum_1[3] = {
  Z3_L_FALSE,
  Z3_L_UNDEF,
  Z3_L_TRUE,
};

void camlidl_ml2c_z3_Z3_lbool(value _v1, Z3_lbool * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_1[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_lbool(Z3_lbool * _c2, camlidl_ctx _ctx)
{
value _v1;
  switch((*_c2)) {
  case Z3_L_FALSE: _v1 = Val_int(0); break;
  case Z3_L_UNDEF: _v1 = Val_int(1); break;
  case Z3_L_TRUE: _v1 = Val_int(2); break;
  default: invalid_argument("typedef Z3_lbool: bad enum  value");
  }
  return _v1;
}

int camlidl_transl_table_z3_enum_2[2] = {
  Z3_INT_SYMBOL,
  Z3_STRING_SYMBOL,
};

void camlidl_ml2c_z3_Z3_symbol_kind(value _v1, Z3_symbol_kind * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_2[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_symbol_kind(Z3_symbol_kind * _c2, camlidl_ctx _ctx)
{
value _v1;
  switch((*_c2)) {
  case Z3_INT_SYMBOL: _v1 = Val_int(0); break;
  case Z3_STRING_SYMBOL: _v1 = Val_int(1); break;
  default: invalid_argument("typedef Z3_symbol_kind: bad enum  value");
  }
  return _v1;
}

int camlidl_transl_table_z3_enum_3[7] = {
  Z3_PARAMETER_INT,
  Z3_PARAMETER_DOUBLE,
  Z3_PARAMETER_RATIONAL,
  Z3_PARAMETER_SYMBOL,
  Z3_PARAMETER_SORT,
  Z3_PARAMETER_AST,
  Z3_PARAMETER_FUNC_DECL,
};

void camlidl_ml2c_z3_Z3_parameter_kind(value _v1, Z3_parameter_kind * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_3[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_parameter_kind(Z3_parameter_kind * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_find_enum((*_c2), camlidl_transl_table_z3_enum_3, 7, "typedef Z3_parameter_kind: bad enum  value");
  return _v1;
}

int camlidl_transl_table_z3_enum_4[10] = {
  Z3_UNINTERPRETED_SORT,
  Z3_BOOL_SORT,
  Z3_INT_SORT,
  Z3_REAL_SORT,
  Z3_BV_SORT,
  Z3_ARRAY_SORT,
  Z3_DATATYPE_SORT,
  Z3_RELATION_SORT,
  Z3_FINITE_DOMAIN_SORT,
  Z3_UNKNOWN_SORT,
};

void camlidl_ml2c_z3_Z3_sort_kind(value _v1, Z3_sort_kind * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_4[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_sort_kind(Z3_sort_kind * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_find_enum((*_c2), camlidl_transl_table_z3_enum_4, 10, "typedef Z3_sort_kind: bad enum  value");
  return _v1;
}

int camlidl_transl_table_z3_enum_5[5] = {
  Z3_NUMERAL_AST,
  Z3_APP_AST,
  Z3_VAR_AST,
  Z3_QUANTIFIER_AST,
  Z3_UNKNOWN_AST,
};

void camlidl_ml2c_z3_Z3_ast_kind(value _v1, Z3_ast_kind * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_5[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_ast_kind(Z3_ast_kind * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_find_enum((*_c2), camlidl_transl_table_z3_enum_5, 5, "typedef Z3_ast_kind: bad enum  value");
  return _v1;
}

int camlidl_transl_table_z3_enum_6[144] = {
  Z3_OP_TRUE,
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
  Z3_OP_ANUM,
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
  Z3_OP_STORE,
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
  Z3_OP_BNUM,
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
  Z3_OP_PR_UNDEF,
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
  Z3_OP_RA_STORE,
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
  Z3_OP_UNINTERPRETED,
};

void camlidl_ml2c_z3_Z3_decl_kind(value _v1, Z3_decl_kind * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_6[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_decl_kind(Z3_decl_kind * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_find_enum((*_c2), camlidl_transl_table_z3_enum_6, 144, "typedef Z3_decl_kind: bad enum  value");
  return _v1;
}

int camlidl_transl_table_z3_enum_7[8] = {
  Z3_NO_FAILURE,
  Z3_UNKNOWN,
  Z3_TIMEOUT,
  Z3_MEMOUT_WATERMARK,
  Z3_CANCELED,
  Z3_NUM_CONFLICTS,
  Z3_THEORY,
  Z3_QUANTIFIERS,
};

void camlidl_ml2c_z3_Z3_search_failure(value _v1, Z3_search_failure * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_7[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_search_failure(Z3_search_failure * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_find_enum((*_c2), camlidl_transl_table_z3_enum_7, 8, "typedef Z3_search_failure: bad enum  value");
  return _v1;
}

int camlidl_transl_table_z3_enum_8[4] = {
  Z3_PRINT_SMTLIB_FULL,
  Z3_PRINT_LOW_LEVEL,
  Z3_PRINT_SMTLIB_COMPLIANT,
  Z3_PRINT_SMTLIB2_COMPLIANT,
};

void camlidl_ml2c_z3_Z3_ast_print_mode(value _v1, Z3_ast_print_mode * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_z3_enum_8[Int_val(_v1)];
}

value camlidl_c2ml_z3_Z3_ast_print_mode(Z3_ast_print_mode * _c2, camlidl_ctx _ctx)
{
value _v1;
  switch((*_c2)) {
  case Z3_PRINT_SMTLIB_FULL: _v1 = Val_int(0); break;
  case Z3_PRINT_LOW_LEVEL: _v1 = Val_int(1); break;
  case Z3_PRINT_SMTLIB_COMPLIANT: _v1 = Val_int(2); break;
  case Z3_PRINT_SMTLIB2_COMPLIANT: _v1 = Val_int(3); break;
  default: invalid_argument("typedef Z3_ast_print_mode: bad enum  value");
  }
  return _v1;
}

value camlidl_z3_Z3_mk_config(value _unit)
{
  Z3_config _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  _res = Z3_mk_config();
  _vres = camlidl_c2ml_z3_Z3_config(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_del_config(
	value _v_c)
{
  Z3_config c; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_config(_v_c, &c, _ctx);
  Z3_del_config(c);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_set_param_value(
	value _v_c,
	value _v_param_id,
	value _v_param_value)
{
  Z3_config c; /*in*/
  char const *param_id; /*in*/
  char const *param_value; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_config(_v_c, &c, _ctx);
  param_id = String_val(_v_param_id);
  param_value = String_val(_v_param_value);
  Z3_set_param_value(c, param_id, param_value);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_mk_context(
	value _v_c)
{
  Z3_config c; /*in*/
  Z3_context _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_config(_v_c, &c, _ctx);
  _res = Z3_mk_context(c);
  _vres = camlidl_c2ml_z3_Z3_context(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
Z3_set_error_handler(_res, caml_z3_error_handler);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_mk_context_rc(
	value _v_c)
{
  Z3_config c; /*in*/
  Z3_context _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_config(_v_c, &c, _ctx);
  _res = Z3_mk_context_rc(c);
  _vres = camlidl_c2ml_z3_Z3_context(&_res, _ctx);
  camlidl_free(_ctx);
  /* begin user-supplied deallocation sequence */
Z3_set_error_handler(_res, caml_z3_error_handler);
  /* end user-supplied deallocation sequence */
  return _vres;
}

value camlidl_z3_Z3_set_logic(
	value _v_c,
	value _v_logic)
{
  Z3_context c; /*in*/
  char const *logic; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  logic = String_val(_v_logic);
  _res = Z3_set_logic(c, logic);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_del_context(
	value _v_c)
{
  Z3_context c; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  Z3_del_context(c);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_inc_ref(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  Z3_inc_ref(c, a);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_dec_ref(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  Z3_dec_ref(c, a);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_trace_to_file(
	value _v_c,
	value _v_trace_file)
{
  Z3_context c; /*in*/
  char const *trace_file; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  trace_file = String_val(_v_trace_file);
  _res = Z3_trace_to_file(c, trace_file);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_trace_to_stderr(
	value _v_c)
{
  Z3_context c; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  Z3_trace_to_stderr(c);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_trace_to_stdout(
	value _v_c)
{
  Z3_context c; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  Z3_trace_to_stdout(c);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_trace_off(
	value _v_c)
{
  Z3_context c; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  Z3_trace_off(c);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_toggle_warning_messages(
	value _v_enabled)
{
  int enabled; /*in*/
  enabled = Int_val(_v_enabled);
  Z3_toggle_warning_messages(enabled);
  return Val_unit;
}

value camlidl_z3_Z3_update_param_value(
	value _v_c,
	value _v_param_id,
	value _v_param_value)
{
  Z3_context c; /*in*/
  char const *param_id; /*in*/
  char const *param_value; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  param_id = String_val(_v_param_id);
  param_value = String_val(_v_param_value);
  Z3_update_param_value(c, param_id, param_value);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_mk_int_symbol(
	value _v_c,
	value _v_i)
{
  Z3_context c; /*in*/
  int i; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  _res = Z3_mk_int_symbol(c, i);
  _vres = camlidl_c2ml_z3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_string_symbol(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  char const *s; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  s = String_val(_v_s);
  _res = Z3_mk_string_symbol(c, s);
  _vres = camlidl_c2ml_z3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_is_eq_sort(
	value _v_c,
	value _v_s1,
	value _v_s2)
{
  Z3_context c; /*in*/
  Z3_sort s1; /*in*/
  Z3_sort s2; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s1, &s1, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s2, &s2, _ctx);
  _res = Z3_is_eq_sort(c, s1, s2);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_uninterpreted_sort(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_s, &s, _ctx);
  _res = Z3_mk_uninterpreted_sort(c, s);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bool_sort(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_bool_sort(c);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_int_sort(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_int_sort(c);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_real_sort(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_real_sort(c);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bv_sort(
	value _v_c,
	value _v_sz)
{
  Z3_context c; /*in*/
  unsigned int sz; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  sz = Int_val(_v_sz);
  _res = Z3_mk_bv_sort(c, sz);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_array_sort(
	value _v_c,
	value _v_domain,
	value _v_range)
{
  Z3_context c; /*in*/
  Z3_sort domain; /*in*/
  Z3_sort range; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_domain, &domain, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_range, &range, _ctx);
  _res = Z3_mk_array_sort(c, domain, range);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_tuple_sort(
	value _v_c,
	value _v_mk_tuple_name,
	value _v_field_names,
	value _v_field_sorts)
{
  Z3_context c; /*in*/
  Z3_symbol mk_tuple_name; /*in*/
  unsigned int num_fields; /*in*/
  Z3_symbol const *field_names; /*in*/
  Z3_sort const *field_sorts; /*in*/
  Z3_func_decl *mk_tuple_decl; /*out*/
  Z3_func_decl *proj_decl; /*out*/
  Z3_sort _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  Z3_func_decl _c7;
  mlsize_t _c8;
  value _v9;
  value _vresult;
  value _vres[3] = { 0, 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_mk_tuple_name, &mk_tuple_name, _ctx);
  _c1 = Wosize_val(_v_field_names);
  field_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_field_names, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &field_names[_c2], _ctx);
  }
  num_fields = _c1;
  _c4 = Wosize_val(_v_field_sorts);
  field_sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_field_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort(_v6, &field_sorts[_c5], _ctx);
  }
  num_fields = _c4;
  mk_tuple_decl = &_c7;
  proj_decl = camlidl_malloc(num_fields * sizeof(Z3_func_decl ), _ctx);
  _res = Z3_mk_tuple_sort(c, mk_tuple_name, num_fields, field_names, field_sorts, mk_tuple_decl, proj_decl);
  Begin_roots_block(_vres, 3)
    _vres[0] = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
    _vres[1] = camlidl_c2ml_z3_Z3_func_decl(&*mk_tuple_decl, _ctx);
    _vres[2] = camlidl_alloc(num_fields, 0);
    Begin_root(_vres[2])
      for (_c8 = 0; _c8 < num_fields; _c8++) {
        _v9 = camlidl_c2ml_z3_Z3_func_decl(&proj_decl[_c8], _ctx);
        modify(&Field(_vres[2], _c8), _v9);
      }
    End_roots()
    _vresult = camlidl_alloc_small(3, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3_Z3_mk_enumeration_sort(
	value _v_c,
	value _v_name,
	value _v_enum_names)
{
  Z3_context c; /*in*/
  Z3_symbol name; /*in*/
  unsigned int n; /*in*/
  Z3_symbol const *enum_names; /*in*/
  Z3_func_decl *enum_consts; /*out*/
  Z3_func_decl *enum_testers; /*out*/
  Z3_sort _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  value _v5;
  mlsize_t _c6;
  value _v7;
  value _vresult;
  value _vres[3] = { 0, 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_name, &name, _ctx);
  _c1 = Wosize_val(_v_enum_names);
  enum_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_enum_names, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &enum_names[_c2], _ctx);
  }
  n = _c1;
  enum_consts = camlidl_malloc(n * sizeof(Z3_func_decl ), _ctx);
  enum_testers = camlidl_malloc(n * sizeof(Z3_func_decl ), _ctx);
  _res = Z3_mk_enumeration_sort(c, name, n, enum_names, enum_consts, enum_testers);
  Begin_roots_block(_vres, 3)
    _vres[0] = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
    _vres[1] = camlidl_alloc(n, 0);
    Begin_root(_vres[1])
      for (_c4 = 0; _c4 < n; _c4++) {
        _v5 = camlidl_c2ml_z3_Z3_func_decl(&enum_consts[_c4], _ctx);
        modify(&Field(_vres[1], _c4), _v5);
      }
    End_roots()
    _vres[2] = camlidl_alloc(n, 0);
    Begin_root(_vres[2])
      for (_c6 = 0; _c6 < n; _c6++) {
        _v7 = camlidl_c2ml_z3_Z3_func_decl(&enum_testers[_c6], _ctx);
        modify(&Field(_vres[2], _c6), _v7);
      }
    End_roots()
    _vresult = camlidl_alloc_small(3, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3_Z3_mk_list_sort(
	value _v_c,
	value _v_name,
	value _v_elem_sort)
{
  Z3_context c; /*in*/
  Z3_symbol name; /*in*/
  Z3_sort elem_sort; /*in*/
  Z3_func_decl *nil_decl; /*out*/
  Z3_func_decl *is_nil_decl; /*out*/
  Z3_func_decl *cons_decl; /*out*/
  Z3_func_decl *is_cons_decl; /*out*/
  Z3_func_decl *head_decl; /*out*/
  Z3_func_decl *tail_decl; /*out*/
  Z3_sort _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  Z3_func_decl _c1;
  Z3_func_decl _c2;
  Z3_func_decl _c3;
  Z3_func_decl _c4;
  Z3_func_decl _c5;
  Z3_func_decl _c6;
  value _vresult;
  value _vres[7] = { 0, 0, 0, 0, 0, 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_name, &name, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_elem_sort, &elem_sort, _ctx);
  nil_decl = &_c1;
  is_nil_decl = &_c2;
  cons_decl = &_c3;
  is_cons_decl = &_c4;
  head_decl = &_c5;
  tail_decl = &_c6;
  _res = Z3_mk_list_sort(c, name, elem_sort, nil_decl, is_nil_decl, cons_decl, is_cons_decl, head_decl, tail_decl);
  Begin_roots_block(_vres, 7)
    _vres[0] = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
    _vres[1] = camlidl_c2ml_z3_Z3_func_decl(&*nil_decl, _ctx);
    _vres[2] = camlidl_c2ml_z3_Z3_func_decl(&*is_nil_decl, _ctx);
    _vres[3] = camlidl_c2ml_z3_Z3_func_decl(&*cons_decl, _ctx);
    _vres[4] = camlidl_c2ml_z3_Z3_func_decl(&*is_cons_decl, _ctx);
    _vres[5] = camlidl_c2ml_z3_Z3_func_decl(&*head_decl, _ctx);
    _vres[6] = camlidl_c2ml_z3_Z3_func_decl(&*tail_decl, _ctx);
    _vresult = camlidl_alloc_small(7, 0);
    { mlsize_t _c7;
      for (_c7 = 0; _c7 < 7; _c7++) Field(_vresult, _c7) = _vres[_c7];
    }
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3_Z3_mk_constructor(
	value _v_c,
	value _v_name,
	value _v_recognizer,
	value _v_field_names,
	value _v_sorts,
	value _v_sort_refs)
{
  Z3_context c; /*in*/
  Z3_symbol name; /*in*/
  Z3_symbol recognizer; /*in*/
  unsigned int num_fields; /*in*/
  Z3_symbol const *field_names; /*in*/
  Z3_sort const *sorts; /*in*/
  unsigned int *sort_refs; /*in*/
  Z3_constructor _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_name, &name, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_recognizer, &recognizer, _ctx);
  _c1 = Wosize_val(_v_field_names);
  field_names = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_field_names, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &field_names[_c2], _ctx);
  }
  num_fields = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_fields = _c4;
  _c7 = Wosize_val(_v_sort_refs);
  sort_refs = camlidl_malloc(_c7 * sizeof(unsigned int ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_sort_refs, _c8);
    sort_refs[_c8] = Int_val(_v9);
  }
  num_fields = _c7;
  _res = Z3_mk_constructor(c, name, recognizer, num_fields, field_names, sorts, sort_refs);
  _vres = camlidl_c2ml_z3_Z3_constructor(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_constructor_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_mk_constructor(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3_Z3_query_constructor(
	value _v_c,
	value _v_constr,
	value _v_num_fields)
{
  Z3_context c; /*in*/
  Z3_constructor constr; /*in*/
  unsigned int num_fields; /*in*/
  Z3_func_decl *constructor; /*out*/
  Z3_func_decl *tester; /*out*/
  Z3_func_decl *accessors; /*out*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  Z3_func_decl _c1;
  Z3_func_decl _c2;
  mlsize_t _c3;
  value _v4;
  value _vresult;
  value _vres[3] = { 0, 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_constructor(_v_constr, &constr, _ctx);
  num_fields = Int_val(_v_num_fields);
  constructor = &_c1;
  tester = &_c2;
  accessors = camlidl_malloc(num_fields * sizeof(Z3_func_decl ), _ctx);
  Z3_query_constructor(c, constr, num_fields, constructor, tester, accessors);
  Begin_roots_block(_vres, 3)
    _vres[0] = camlidl_c2ml_z3_Z3_func_decl(&*constructor, _ctx);
    _vres[1] = camlidl_c2ml_z3_Z3_func_decl(&*tester, _ctx);
    _vres[2] = camlidl_alloc(num_fields, 0);
    Begin_root(_vres[2])
      for (_c3 = 0; _c3 < num_fields; _c3++) {
        _v4 = camlidl_c2ml_z3_Z3_func_decl(&accessors[_c3], _ctx);
        modify(&Field(_vres[2], _c3), _v4);
      }
    End_roots()
    _vresult = camlidl_alloc_small(3, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3_Z3_del_constructor(
	value _v_c,
	value _v_constr)
{
  Z3_context c; /*in*/
  Z3_constructor constr; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_constructor(_v_constr, &constr, _ctx);
  Z3_del_constructor(c, constr);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_mk_datatype(
	value _v_c,
	value _v_name,
	value _v_constructors)
{
  Z3_context c; /*in*/
  Z3_symbol name; /*in*/
  unsigned int num_constructors; /*in*/
  Z3_constructor *constructors; /*in,out*/
  Z3_sort _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  value _v5;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_name, &name, _ctx);
  _c1 = Wosize_val(_v_constructors);
  constructors = camlidl_malloc(_c1 * sizeof(Z3_constructor ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_constructors, _c2);
    camlidl_ml2c_z3_Z3_constructor(_v3, &constructors[_c2], _ctx);
  }
  num_constructors = _c1;
  _res = Z3_mk_datatype(c, name, num_constructors, constructors);
  Begin_roots_block(_vres, 2)
    _vres[0] = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
    _vres[1] = camlidl_alloc(num_constructors, 0);
    Begin_root(_vres[1])
      for (_c4 = 0; _c4 < num_constructors; _c4++) {
        _v5 = camlidl_c2ml_z3_Z3_constructor(&constructors[_c4], _ctx);
        modify(&Field(_vres[1], _c4), _v5);
      }
    End_roots()
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3_Z3_mk_constructor_list(
	value _v_c,
	value _v_constructors)
{
  Z3_context c; /*in*/
  unsigned int num_constructors; /*in*/
  Z3_constructor *constructors; /*in*/
  Z3_constructor_list _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_constructors);
  constructors = camlidl_malloc(_c1 * sizeof(Z3_constructor ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_constructors, _c2);
    camlidl_ml2c_z3_Z3_constructor(_v3, &constructors[_c2], _ctx);
  }
  num_constructors = _c1;
  _res = Z3_mk_constructor_list(c, num_constructors, constructors);
  _vres = camlidl_c2ml_z3_Z3_constructor_list(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_del_constructor_list(
	value _v_c,
	value _v_clist)
{
  Z3_context c; /*in*/
  Z3_constructor_list clist; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_constructor_list(_v_clist, &clist, _ctx);
  Z3_del_constructor_list(c, clist);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_mk_datatypes(
	value _v_c,
	value _v_sort_names,
	value _v_constructor_lists)
{
  Z3_context c; /*in*/
  unsigned int num_sorts; /*in*/
  Z3_symbol *sort_names; /*in*/
  Z3_sort *sorts; /*out*/
  Z3_constructor_list *constructor_lists; /*in,out*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  value _v8;
  mlsize_t _c9;
  value _v10;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_sort_names);
  sort_names = camlidl_malloc(_c1 * sizeof(Z3_symbol ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_sort_names, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &sort_names[_c2], _ctx);
  }
  num_sorts = _c1;
  _c4 = Wosize_val(_v_constructor_lists);
  constructor_lists = camlidl_malloc(_c4 * sizeof(Z3_constructor_list ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_constructor_lists, _c5);
    camlidl_ml2c_z3_Z3_constructor_list(_v6, &constructor_lists[_c5], _ctx);
  }
  num_sorts = _c4;
  sorts = camlidl_malloc(num_sorts * sizeof(Z3_sort ), _ctx);
  Z3_mk_datatypes(c, num_sorts, sort_names, sorts, constructor_lists);
  Begin_roots_block(_vres, 2)
    _vres[0] = camlidl_alloc(num_sorts, 0);
    Begin_root(_vres[0])
      for (_c7 = 0; _c7 < num_sorts; _c7++) {
        _v8 = camlidl_c2ml_z3_Z3_sort(&sorts[_c7], _ctx);
        modify(&Field(_vres[0], _c7), _v8);
      }
    End_roots()
    _vres[1] = camlidl_alloc(num_sorts, 0);
    Begin_root(_vres[1])
      for (_c9 = 0; _c9 < num_sorts; _c9++) {
        _v10 = camlidl_c2ml_z3_Z3_constructor_list(&constructor_lists[_c9], _ctx);
        modify(&Field(_vres[1], _c9), _v10);
      }
    End_roots()
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3_Z3_mk_injective_function(
	value _v_c,
	value _v_s,
	value _v_domain,
	value _v_range)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  unsigned int domain_size; /*in*/
  Z3_sort const *domain; /*in*/
  Z3_sort range; /*in*/
  Z3_func_decl _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_s, &s, _ctx);
  _c1 = Wosize_val(_v_domain);
  domain = camlidl_malloc(_c1 * sizeof(Z3_sort const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_domain, _c2);
    camlidl_ml2c_z3_Z3_sort(_v3, &domain[_c2], _ctx);
  }
  domain_size = _c1;
  camlidl_ml2c_z3_Z3_sort(_v_range, &range, _ctx);
  _res = Z3_mk_injective_function(c, s, domain_size, domain, range);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_is_eq_ast(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_is_eq_ast(c, t1, t2);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_is_eq_func_decl(
	value _v_c,
	value _v_f1,
	value _v_f2)
{
  Z3_context c; /*in*/
  Z3_func_decl f1; /*in*/
  Z3_func_decl f2; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_f1, &f1, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_f2, &f2, _ctx);
  _res = Z3_is_eq_func_decl(c, f1, f2);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_func_decl(
	value _v_c,
	value _v_s,
	value _v_domain,
	value _v_range)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  unsigned int domain_size; /*in*/
  Z3_sort const *domain; /*in*/
  Z3_sort range; /*in*/
  Z3_func_decl _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_s, &s, _ctx);
  _c1 = Wosize_val(_v_domain);
  domain = camlidl_malloc(_c1 * sizeof(Z3_sort const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_domain, _c2);
    camlidl_ml2c_z3_Z3_sort(_v3, &domain[_c2], _ctx);
  }
  domain_size = _c1;
  camlidl_ml2c_z3_Z3_sort(_v_range, &range, _ctx);
  _res = Z3_mk_func_decl(c, s, domain_size, domain, range);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_app(
	value _v_c,
	value _v_d,
	value _v_args)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_app(c, d, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_const(
	value _v_c,
	value _v_s,
	value _v_ty)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_s, &s, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_const(c, s, ty);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_label(
	value _v_c,
	value _v_s,
	value _v_is_pos,
	value _v_f)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  int is_pos; /*in*/
  Z3_ast f; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_s, &s, _ctx);
  is_pos = Int_val(_v_is_pos);
  camlidl_ml2c_z3_Z3_ast(_v_f, &f, _ctx);
  _res = Z3_mk_label(c, s, is_pos, f);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_fresh_func_decl(
	value _v_c,
	value _v_prefix,
	value _v_domain,
	value _v_range)
{
  Z3_context c; /*in*/
  char const *prefix; /*in*/
  unsigned int domain_size; /*in*/
  Z3_sort const *domain; /*in*/
  Z3_sort range; /*in*/
  Z3_func_decl _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  prefix = String_val(_v_prefix);
  _c1 = Wosize_val(_v_domain);
  domain = camlidl_malloc(_c1 * sizeof(Z3_sort const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_domain, _c2);
    camlidl_ml2c_z3_Z3_sort(_v3, &domain[_c2], _ctx);
  }
  domain_size = _c1;
  camlidl_ml2c_z3_Z3_sort(_v_range, &range, _ctx);
  _res = Z3_mk_fresh_func_decl(c, prefix, domain_size, domain, range);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_fresh_const(
	value _v_c,
	value _v_prefix,
	value _v_ty)
{
  Z3_context c; /*in*/
  char const *prefix; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  prefix = String_val(_v_prefix);
  camlidl_ml2c_z3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_fresh_const(c, prefix, ty);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_true(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_true(c);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_false(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_mk_false(c);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_eq(
	value _v_c,
	value _v_l,
	value _v_r)
{
  Z3_context c; /*in*/
  Z3_ast l; /*in*/
  Z3_ast r; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_l, &l, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_r, &r, _ctx);
  _res = Z3_mk_eq(c, l, r);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_distinct(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_distinct(c, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_not(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_mk_not(c, a);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_ite(
	value _v_c,
	value _v_t1,
	value _v_t2,
	value _v_t3)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast t3; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t3, &t3, _ctx);
  _res = Z3_mk_ite(c, t1, t2, t3);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_iff(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_iff(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_implies(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_implies(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_xor(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_xor(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_and(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_and(c, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_or(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_or(c, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_add(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_add(c, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_mul(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_mul(c, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_sub(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_sub(c, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_unary_minus(
	value _v_c,
	value _v_arg)
{
  Z3_context c; /*in*/
  Z3_ast arg; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg, &arg, _ctx);
  _res = Z3_mk_unary_minus(c, arg);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_div(
	value _v_c,
	value _v_arg1,
	value _v_arg2)
{
  Z3_context c; /*in*/
  Z3_ast arg1; /*in*/
  Z3_ast arg2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg1, &arg1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg2, &arg2, _ctx);
  _res = Z3_mk_div(c, arg1, arg2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_mod(
	value _v_c,
	value _v_arg1,
	value _v_arg2)
{
  Z3_context c; /*in*/
  Z3_ast arg1; /*in*/
  Z3_ast arg2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg1, &arg1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg2, &arg2, _ctx);
  _res = Z3_mk_mod(c, arg1, arg2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_rem(
	value _v_c,
	value _v_arg1,
	value _v_arg2)
{
  Z3_context c; /*in*/
  Z3_ast arg1; /*in*/
  Z3_ast arg2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg1, &arg1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg2, &arg2, _ctx);
  _res = Z3_mk_rem(c, arg1, arg2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_lt(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_lt(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_le(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_le(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_gt(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_gt(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_ge(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_ge(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_int2real(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_int2real(c, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_real2int(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_real2int(c, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_is_int(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_is_int(c, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvnot(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_bvnot(c, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvredand(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_bvredand(c, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvredor(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_bvredor(c, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvand(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvand(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvor(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvor(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvxor(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvxor(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvnand(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvnand(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvnor(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvnor(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvxnor(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvxnor(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvneg(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_bvneg(c, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvadd(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvadd(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvsub(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsub(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvmul(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvmul(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvudiv(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvudiv(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvsdiv(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsdiv(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvurem(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvurem(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvsrem(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsrem(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvsmod(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsmod(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvult(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvult(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvslt(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvslt(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvule(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvule(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvsle(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsle(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvuge(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvuge(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvsge(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsge(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvugt(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvugt(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvsgt(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsgt(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_concat(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_concat(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_extract(
	value _v_c,
	value _v_high,
	value _v_low,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int high; /*in*/
  unsigned int low; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  high = Int_val(_v_high);
  low = Int_val(_v_low);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_extract(c, high, low, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_sign_ext(
	value _v_c,
	value _v_i,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_sign_ext(c, i, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_zero_ext(
	value _v_c,
	value _v_i,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_zero_ext(c, i, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_repeat(
	value _v_c,
	value _v_i,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_repeat(c, i, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvshl(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvshl(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvlshr(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvlshr(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvashr(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvashr(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_rotate_left(
	value _v_c,
	value _v_i,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_rotate_left(c, i, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_rotate_right(
	value _v_c,
	value _v_i,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_rotate_right(c, i, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_ext_rotate_left(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_ext_rotate_left(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_ext_rotate_right(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_ext_rotate_right(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_int2bv(
	value _v_c,
	value _v_n,
	value _v_t1)
{
  Z3_context c; /*in*/
  unsigned int n; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  n = Int_val(_v_n);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_int2bv(c, n, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bv2int(
	value _v_c,
	value _v_t1,
	value _v_is_signed)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  int is_signed; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  is_signed = Int_val(_v_is_signed);
  _res = Z3_mk_bv2int(c, t1, is_signed);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvadd_no_overflow(
	value _v_c,
	value _v_t1,
	value _v_t2,
	value _v_is_signed)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  int is_signed; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  is_signed = Int_val(_v_is_signed);
  _res = Z3_mk_bvadd_no_overflow(c, t1, t2, is_signed);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvadd_no_underflow(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvadd_no_underflow(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvsub_no_overflow(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsub_no_overflow(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvsub_no_underflow(
	value _v_c,
	value _v_t1,
	value _v_t2,
	value _v_is_signed)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  int is_signed; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  is_signed = Int_val(_v_is_signed);
  _res = Z3_mk_bvsub_no_underflow(c, t1, t2, is_signed);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvsdiv_no_overflow(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvsdiv_no_overflow(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvneg_no_overflow(
	value _v_c,
	value _v_t1)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  _res = Z3_mk_bvneg_no_overflow(c, t1);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvmul_no_overflow(
	value _v_c,
	value _v_t1,
	value _v_t2,
	value _v_is_signed)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  int is_signed; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  is_signed = Int_val(_v_is_signed);
  _res = Z3_mk_bvmul_no_overflow(c, t1, t2, is_signed);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bvmul_no_underflow(
	value _v_c,
	value _v_t1,
	value _v_t2)
{
  Z3_context c; /*in*/
  Z3_ast t1; /*in*/
  Z3_ast t2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t1, &t1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t2, &t2, _ctx);
  _res = Z3_mk_bvmul_no_underflow(c, t1, t2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_select(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_i, &i, _ctx);
  _res = Z3_mk_select(c, a, i);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_store(
	value _v_c,
	value _v_a,
	value _v_i,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast i; /*in*/
  Z3_ast v; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_i, &i, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_v, &v, _ctx);
  _res = Z3_mk_store(c, a, i, v);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_const_array(
	value _v_c,
	value _v_domain,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_sort domain; /*in*/
  Z3_ast v; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_domain, &domain, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_v, &v, _ctx);
  _res = Z3_mk_const_array(c, domain, v);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_map(
	value _v_c,
	value _v_f,
	value _v_n,
	value _v_args)
{
  Z3_context c; /*in*/
  Z3_func_decl f; /*in*/
  unsigned int n; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  Z3_ast _c1;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_f, &f, _ctx);
  n = Int_val(_v_n);
  args = &_c1;
  camlidl_ml2c_z3_Z3_ast(_v_args, &_c1, _ctx);
  _res = Z3_mk_map(c, f, n, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_array_default(
	value _v_c,
	value _v_array)
{
  Z3_context c; /*in*/
  Z3_ast array; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_array, &array, _ctx);
  _res = Z3_mk_array_default(c, array);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_set_sort(
	value _v_c,
	value _v_ty)
{
  Z3_context c; /*in*/
  Z3_sort ty; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_set_sort(c, ty);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_empty_set(
	value _v_c,
	value _v_domain)
{
  Z3_context c; /*in*/
  Z3_sort domain; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_domain, &domain, _ctx);
  _res = Z3_mk_empty_set(c, domain);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_full_set(
	value _v_c,
	value _v_domain)
{
  Z3_context c; /*in*/
  Z3_sort domain; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_domain, &domain, _ctx);
  _res = Z3_mk_full_set(c, domain);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_set_add(
	value _v_c,
	value _v_set,
	value _v_elem)
{
  Z3_context c; /*in*/
  Z3_ast set; /*in*/
  Z3_ast elem; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_set, &set, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_elem, &elem, _ctx);
  _res = Z3_mk_set_add(c, set, elem);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_set_del(
	value _v_c,
	value _v_set,
	value _v_elem)
{
  Z3_context c; /*in*/
  Z3_ast set; /*in*/
  Z3_ast elem; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_set, &set, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_elem, &elem, _ctx);
  _res = Z3_mk_set_del(c, set, elem);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_set_union(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_set_union(c, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_set_intersect(
	value _v_c,
	value _v_args)
{
  Z3_context c; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast const *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_mk_set_intersect(c, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_set_difference(
	value _v_c,
	value _v_arg1,
	value _v_arg2)
{
  Z3_context c; /*in*/
  Z3_ast arg1; /*in*/
  Z3_ast arg2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg1, &arg1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg2, &arg2, _ctx);
  _res = Z3_mk_set_difference(c, arg1, arg2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_set_complement(
	value _v_c,
	value _v_arg)
{
  Z3_context c; /*in*/
  Z3_ast arg; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg, &arg, _ctx);
  _res = Z3_mk_set_complement(c, arg);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_set_member(
	value _v_c,
	value _v_elem,
	value _v_set)
{
  Z3_context c; /*in*/
  Z3_ast elem; /*in*/
  Z3_ast set; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_elem, &elem, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_set, &set, _ctx);
  _res = Z3_mk_set_member(c, elem, set);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_set_subset(
	value _v_c,
	value _v_arg1,
	value _v_arg2)
{
  Z3_context c; /*in*/
  Z3_ast arg1; /*in*/
  Z3_ast arg2; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg1, &arg1, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_arg2, &arg2, _ctx);
  _res = Z3_mk_set_subset(c, arg1, arg2);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_numeral(
	value _v_c,
	value _v_numeral,
	value _v_ty)
{
  Z3_context c; /*in*/
  char const *numeral; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  numeral = String_val(_v_numeral);
  camlidl_ml2c_z3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_numeral(c, numeral, ty);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_real(
	value _v_c,
	value _v_num,
	value _v_den)
{
  Z3_context c; /*in*/
  int num; /*in*/
  int den; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  num = Int_val(_v_num);
  den = Int_val(_v_den);
  _res = Z3_mk_real(c, num, den);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_int(
	value _v_c,
	value _v_v,
	value _v_ty)
{
  Z3_context c; /*in*/
  int v; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  v = Int_val(_v_v);
  camlidl_ml2c_z3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_int(c, v, ty);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_unsigned_int(
	value _v_c,
	value _v_v,
	value _v_ty)
{
  Z3_context c; /*in*/
  unsigned int v; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  v = Int_val(_v_v);
  camlidl_ml2c_z3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_unsigned_int(c, v, ty);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_pattern(
	value _v_c,
	value _v_terms)
{
  Z3_context c; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_ast const *terms; /*in*/
  Z3_pattern _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_terms);
  terms = camlidl_malloc(_c1 * sizeof(Z3_ast const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_terms, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &terms[_c2], _ctx);
  }
  num_patterns = _c1;
  _res = Z3_mk_pattern(c, num_patterns, terms);
  _vres = camlidl_c2ml_z3_Z3_pattern(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_bound(
	value _v_c,
	value _v_index,
	value _v_ty)
{
  Z3_context c; /*in*/
  unsigned int index; /*in*/
  Z3_sort ty; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  index = Int_val(_v_index);
  camlidl_ml2c_z3_Z3_sort(_v_ty, &ty, _ctx);
  _res = Z3_mk_bound(c, index, ty);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_forall(
	value _v_c,
	value _v_weight,
	value _v_patterns,
	value _v_sorts,
	value _v_decl_names,
	value _v_body)
{
  Z3_context c; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  unsigned int num_decls; /*in*/
  Z3_sort const *sorts; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c1 * sizeof(Z3_pattern const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_patterns, _c2);
    camlidl_ml2c_z3_Z3_pattern(_v3, &patterns[_c2], _ctx);
  }
  num_patterns = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_decls = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  camlidl_ml2c_z3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_forall(c, weight, num_patterns, patterns, num_decls, sorts, decl_names, body);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_forall_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_mk_forall(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3_Z3_mk_exists(
	value _v_c,
	value _v_weight,
	value _v_patterns,
	value _v_sorts,
	value _v_decl_names,
	value _v_body)
{
  Z3_context c; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  unsigned int num_decls; /*in*/
  Z3_sort const *sorts; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c1 * sizeof(Z3_pattern const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_patterns, _c2);
    camlidl_ml2c_z3_Z3_pattern(_v3, &patterns[_c2], _ctx);
  }
  num_patterns = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_decls = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  camlidl_ml2c_z3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_exists(c, weight, num_patterns, patterns, num_decls, sorts, decl_names, body);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_exists_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_mk_exists(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3_Z3_mk_quantifier(
	value _v_c,
	value _v_is_forall,
	value _v_weight,
	value _v_patterns,
	value _v_sorts,
	value _v_decl_names,
	value _v_body)
{
  Z3_context c; /*in*/
  int is_forall; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  unsigned int num_decls; /*in*/
  Z3_sort const *sorts; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  is_forall = Int_val(_v_is_forall);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c1 * sizeof(Z3_pattern const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_patterns, _c2);
    camlidl_ml2c_z3_Z3_pattern(_v3, &patterns[_c2], _ctx);
  }
  num_patterns = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_decls = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  camlidl_ml2c_z3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_quantifier(c, is_forall, weight, num_patterns, patterns, num_decls, sorts, decl_names, body);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_quantifier_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_mk_quantifier(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6]);
}

value camlidl_z3_Z3_mk_quantifier_ex(
	value _v_c,
	value _v_is_forall,
	value _v_weight,
	value _v_quantifier_id,
	value _v_skolem_id,
	value _v_patterns,
	value _v_no_patterns,
	value _v_sorts,
	value _v_decl_names,
	value _v_body)
{
  Z3_context c; /*in*/
  int is_forall; /*in*/
  unsigned int weight; /*in*/
  Z3_symbol quantifier_id; /*in*/
  Z3_symbol skolem_id; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  unsigned int num_no_patterns; /*in*/
  Z3_ast const *no_patterns; /*in*/
  unsigned int num_decls; /*in*/
  Z3_sort const *sorts; /*in*/
  Z3_symbol const *decl_names; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  mlsize_t _c10;
  mlsize_t _c11;
  value _v12;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  is_forall = Int_val(_v_is_forall);
  weight = Int_val(_v_weight);
  camlidl_ml2c_z3_Z3_symbol(_v_quantifier_id, &quantifier_id, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_skolem_id, &skolem_id, _ctx);
  _c1 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c1 * sizeof(Z3_pattern const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_patterns, _c2);
    camlidl_ml2c_z3_Z3_pattern(_v3, &patterns[_c2], _ctx);
  }
  num_patterns = _c1;
  _c4 = Wosize_val(_v_no_patterns);
  no_patterns = camlidl_malloc(_c4 * sizeof(Z3_ast const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_no_patterns, _c5);
    camlidl_ml2c_z3_Z3_ast(_v6, &no_patterns[_c5], _ctx);
  }
  num_no_patterns = _c4;
  _c7 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c7 * sizeof(Z3_sort const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_sorts, _c8);
    camlidl_ml2c_z3_Z3_sort(_v9, &sorts[_c8], _ctx);
  }
  num_decls = _c7;
  _c10 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c10 * sizeof(Z3_symbol const ), _ctx);
  for (_c11 = 0; _c11 < _c10; _c11++) {
    _v12 = Field(_v_decl_names, _c11);
    camlidl_ml2c_z3_Z3_symbol(_v12, &decl_names[_c11], _ctx);
  }
  num_decls = _c10;
  camlidl_ml2c_z3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_quantifier_ex(c, is_forall, weight, quantifier_id, skolem_id, num_patterns, patterns, num_no_patterns, no_patterns, num_decls, sorts, decl_names, body);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_quantifier_ex_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_mk_quantifier_ex(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7], argv[8], argv[9]);
}

value camlidl_z3_Z3_mk_forall_const(
	value _v_c,
	value _v_weight,
	value _v_bound,
	value _v_patterns,
	value _v_body)
{
  Z3_context c; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_bound; /*in*/
  Z3_app const *bound; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_bound);
  bound = camlidl_malloc(_c1 * sizeof(Z3_app const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_bound, _c2);
    camlidl_ml2c_z3_Z3_app(_v3, &bound[_c2], _ctx);
  }
  num_bound = _c1;
  _c4 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c4 * sizeof(Z3_pattern const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_patterns, _c5);
    camlidl_ml2c_z3_Z3_pattern(_v6, &patterns[_c5], _ctx);
  }
  num_patterns = _c4;
  camlidl_ml2c_z3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_forall_const(c, weight, num_bound, bound, num_patterns, patterns, body);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_exists_const(
	value _v_c,
	value _v_weight,
	value _v_bound,
	value _v_patterns,
	value _v_body)
{
  Z3_context c; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_bound; /*in*/
  Z3_app const *bound; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_bound);
  bound = camlidl_malloc(_c1 * sizeof(Z3_app const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_bound, _c2);
    camlidl_ml2c_z3_Z3_app(_v3, &bound[_c2], _ctx);
  }
  num_bound = _c1;
  _c4 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c4 * sizeof(Z3_pattern const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_patterns, _c5);
    camlidl_ml2c_z3_Z3_pattern(_v6, &patterns[_c5], _ctx);
  }
  num_patterns = _c4;
  camlidl_ml2c_z3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_exists_const(c, weight, num_bound, bound, num_patterns, patterns, body);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_quantifier_const(
	value _v_c,
	value _v_is_forall,
	value _v_weight,
	value _v_bound,
	value _v_patterns,
	value _v_body)
{
  Z3_context c; /*in*/
  int is_forall; /*in*/
  unsigned int weight; /*in*/
  unsigned int num_bound; /*in*/
  Z3_app const *bound; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  is_forall = Int_val(_v_is_forall);
  weight = Int_val(_v_weight);
  _c1 = Wosize_val(_v_bound);
  bound = camlidl_malloc(_c1 * sizeof(Z3_app const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_bound, _c2);
    camlidl_ml2c_z3_Z3_app(_v3, &bound[_c2], _ctx);
  }
  num_bound = _c1;
  _c4 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c4 * sizeof(Z3_pattern const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_patterns, _c5);
    camlidl_ml2c_z3_Z3_pattern(_v6, &patterns[_c5], _ctx);
  }
  num_patterns = _c4;
  camlidl_ml2c_z3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_quantifier_const(c, is_forall, weight, num_bound, bound, num_patterns, patterns, body);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_quantifier_const_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_mk_quantifier_const(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3_Z3_mk_quantifier_const_ex(
	value _v_c,
	value _v_is_forall,
	value _v_weight,
	value _v_quantifier_id,
	value _v_skolem_id,
	value _v_bound,
	value _v_patterns,
	value _v_no_patterns,
	value _v_body)
{
  Z3_context c; /*in*/
  int is_forall; /*in*/
  unsigned int weight; /*in*/
  Z3_symbol quantifier_id; /*in*/
  Z3_symbol skolem_id; /*in*/
  unsigned int num_bound; /*in*/
  Z3_app const *bound; /*in*/
  unsigned int num_patterns; /*in*/
  Z3_pattern const *patterns; /*in*/
  unsigned int num_no_patterns; /*in*/
  Z3_ast const *no_patterns; /*in*/
  Z3_ast body; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  is_forall = Int_val(_v_is_forall);
  weight = Int_val(_v_weight);
  camlidl_ml2c_z3_Z3_symbol(_v_quantifier_id, &quantifier_id, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_skolem_id, &skolem_id, _ctx);
  _c1 = Wosize_val(_v_bound);
  bound = camlidl_malloc(_c1 * sizeof(Z3_app const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_bound, _c2);
    camlidl_ml2c_z3_Z3_app(_v3, &bound[_c2], _ctx);
  }
  num_bound = _c1;
  _c4 = Wosize_val(_v_patterns);
  patterns = camlidl_malloc(_c4 * sizeof(Z3_pattern const ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_patterns, _c5);
    camlidl_ml2c_z3_Z3_pattern(_v6, &patterns[_c5], _ctx);
  }
  num_patterns = _c4;
  _c7 = Wosize_val(_v_no_patterns);
  no_patterns = camlidl_malloc(_c7 * sizeof(Z3_ast const ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_no_patterns, _c8);
    camlidl_ml2c_z3_Z3_ast(_v9, &no_patterns[_c8], _ctx);
  }
  num_no_patterns = _c7;
  camlidl_ml2c_z3_Z3_ast(_v_body, &body, _ctx);
  _res = Z3_mk_quantifier_const_ex(c, is_forall, weight, quantifier_id, skolem_id, num_bound, bound, num_patterns, patterns, num_no_patterns, no_patterns, body);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_mk_quantifier_const_ex_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_mk_quantifier_const_ex(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7], argv[8]);
}

value camlidl_z3_Z3_get_ast_id(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_ast t; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t, &t, _ctx);
  _res = Z3_get_ast_id(c, t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_func_decl_id(
	value _v_c,
	value _v_f)
{
  Z3_context c; /*in*/
  Z3_func_decl f; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_f, &f, _ctx);
  _res = Z3_get_func_decl_id(c, f);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_sort_id(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_sort s; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s, &s, _ctx);
  _res = Z3_get_sort_id(c, s);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_is_well_sorted(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_ast t; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t, &t, _ctx);
  _res = Z3_is_well_sorted(c, t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_symbol_kind(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  Z3_symbol_kind _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_s, &s, _ctx);
  _res = Z3_get_symbol_kind(c, s);
  _vres = camlidl_c2ml_z3_Z3_symbol_kind(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_symbol_int(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_s, &s, _ctx);
  _res = Z3_get_symbol_int(c, s);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_symbol_string(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_symbol s; /*in*/
  char const *_res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_s, &s, _ctx);
  _res = Z3_get_symbol_string(c, s);
  _vres = copy_string(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_ast_kind(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast_kind _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_ast_kind(c, a);
  _vres = camlidl_c2ml_z3_Z3_ast_kind(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_numeral_string(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  char const *_res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_numeral_string(c, a);
  _vres = copy_string(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_numeral_small(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  __int64 *num; /*out*/
  __int64 *den; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  __int64 _c1;
  __int64 _c2;
  value _vresult;
  value _vres[3] = { 0, 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  num = &_c1;
  den = &_c2;
  _res = Z3_get_numeral_small(c, a, num, den);
  Begin_roots_block(_vres, 3)
    _vres[0] = Val_int(_res);
    _vres[1] = copy_int64(*num);
    _vres[2] = copy_int64(*den);
    _vresult = camlidl_alloc_small(3, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3_Z3_get_numeral_int(
	value _v_c,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_ast v; /*in*/
  int *i; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  int _c1;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_v, &v, _ctx);
  i = &_c1;
  _res = Z3_get_numeral_int(c, v, i);
  Begin_roots_block(_vres, 2)
    _vres[0] = Val_int(_res);
    _vres[1] = Val_int(*i);
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3_Z3_get_numeral_uint(
	value _v_c,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_ast v; /*in*/
  unsigned int *u; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  unsigned int _c1;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_v, &v, _ctx);
  u = &_c1;
  _res = Z3_get_numeral_uint(c, v, u);
  Begin_roots_block(_vres, 2)
    _vres[0] = Val_int(_res);
    _vres[1] = Val_int(*u);
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3_Z3_get_bool_value(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_lbool _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_bool_value(c, a);
  _vres = camlidl_c2ml_z3_Z3_lbool(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_app_decl(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_app a; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_app(_v_a, &a, _ctx);
  _res = Z3_get_app_decl(c, a);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_app_num_args(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_app a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_app(_v_a, &a, _ctx);
  _res = Z3_get_app_num_args(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_app_arg(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_app a; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_app(_v_a, &a, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_app_arg(c, a, i);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_index_value(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_index_value(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_is_quantifier_forall(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_is_quantifier_forall(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_weight(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_quantifier_weight(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_num_patterns(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_quantifier_num_patterns(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_pattern_ast(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int i; /*in*/
  Z3_pattern _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_quantifier_pattern_ast(c, a, i);
  _vres = camlidl_c2ml_z3_Z3_pattern(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_num_no_patterns(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_quantifier_num_no_patterns(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_no_pattern_ast(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_quantifier_no_pattern_ast(c, a, i);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_bound_name(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int i; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_quantifier_bound_name(c, a, i);
  _vres = camlidl_c2ml_z3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_bound_sort(
	value _v_c,
	value _v_a,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int i; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_quantifier_bound_sort(c, a, i);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_body(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_quantifier_body(c, a);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_quantifier_num_bound(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_quantifier_num_bound(c, a);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_decl_name(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_get_decl_name(c, d);
  _vres = camlidl_c2ml_z3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_decl_num_parameters(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_get_decl_num_parameters(c, d);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_decl_parameter_kind(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  Z3_parameter_kind _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_parameter_kind(c, d, idx);
  _vres = camlidl_c2ml_z3_Z3_parameter_kind(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_decl_int_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_int_parameter(c, d, idx);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_decl_double_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  double _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_double_parameter(c, d, idx);
  _vres = copy_double(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_decl_symbol_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_symbol_parameter(c, d, idx);
  _vres = camlidl_c2ml_z3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_decl_sort_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_sort_parameter(c, d, idx);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_decl_ast_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_ast_parameter(c, d, idx);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_decl_func_decl_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_func_decl_parameter(c, d, idx);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_decl_rational_parameter(
	value _v_c,
	value _v_d,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int idx; /*in*/
  char const *_res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_decl_rational_parameter(c, d, idx);
  _vres = copy_string(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_sort_name(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_sort d; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_d, &d, _ctx);
  _res = Z3_get_sort_name(c, d);
  _vres = camlidl_c2ml_z3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_sort(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_get_sort(c, a);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_domain_size(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_get_domain_size(c, d);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_domain(
	value _v_c,
	value _v_d,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int i; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_domain(c, d, i);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_range(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_get_range(c, d);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_sort_kind(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  Z3_sort_kind _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_sort_kind(c, t);
  _vres = camlidl_c2ml_z3_Z3_sort_kind(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_bv_sort_size(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_bv_sort_size(c, t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_array_sort_domain(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_array_sort_domain(c, t);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_array_sort_range(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_array_sort_range(c, t);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_tuple_sort_mk_decl(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_tuple_sort_mk_decl(c, t);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_decl_kind(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  Z3_decl_kind _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_get_decl_kind(c, d);
  _vres = camlidl_c2ml_z3_Z3_decl_kind(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_tuple_sort_num_fields(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_tuple_sort_num_fields(c, t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_tuple_sort_field_decl(
	value _v_c,
	value _v_t,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int i; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_tuple_sort_field_decl(c, t, i);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_datatype_sort_num_constructors(
	value _v_c,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  _res = Z3_get_datatype_sort_num_constructors(c, t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_datatype_sort_constructor(
	value _v_c,
	value _v_t,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int idx; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_datatype_sort_constructor(c, t, idx);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_datatype_sort_recognizer(
	value _v_c,
	value _v_t,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int idx; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_datatype_sort_recognizer(c, t, idx);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_datatype_sort_constructor_accessor(
	value _v_c,
	value _v_t,
	value _v_idx_c,
	value _v_idx_a)
{
  Z3_context c; /*in*/
  Z3_sort t; /*in*/
  unsigned int idx_c; /*in*/
  unsigned int idx_a; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_t, &t, _ctx);
  idx_c = Int_val(_v_idx_c);
  idx_a = Int_val(_v_idx_a);
  _res = Z3_get_datatype_sort_constructor_accessor(c, t, idx_c, idx_a);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_relation_arity(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_sort s; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s, &s, _ctx);
  _res = Z3_get_relation_arity(c, s);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_relation_column(
	value _v_c,
	value _v_s,
	value _v_col)
{
  Z3_context c; /*in*/
  Z3_sort s; /*in*/
  unsigned int col; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s, &s, _ctx);
  col = Int_val(_v_col);
  _res = Z3_get_relation_column(c, s, col);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_pattern_num_terms(
	value _v_c,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_pattern p; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_pattern(_v_p, &p, _ctx);
  _res = Z3_get_pattern_num_terms(c, p);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_pattern(
	value _v_c,
	value _v_p,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_pattern p; /*in*/
  unsigned int idx; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_pattern(_v_p, &p, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_pattern(c, p, idx);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_simplify(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_simplify(c, a);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_update_term(
	value _v_c,
	value _v_a,
	value _v_args)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast *args; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  _res = Z3_update_term(c, a, num_args, args);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_substitute(
	value _v_c,
	value _v_a,
	value _v_from,
	value _v_to)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int num_exprs; /*in*/
  Z3_ast *from; /*in*/
  Z3_ast *to; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _c1 = Wosize_val(_v_from);
  from = camlidl_malloc(_c1 * sizeof(Z3_ast ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_from, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &from[_c2], _ctx);
  }
  num_exprs = _c1;
  _c4 = Wosize_val(_v_to);
  to = camlidl_malloc(_c4 * sizeof(Z3_ast ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_to, _c5);
    camlidl_ml2c_z3_Z3_ast(_v6, &to[_c5], _ctx);
  }
  num_exprs = _c4;
  _res = Z3_substitute(c, a, num_exprs, from, to);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_substitute_vars(
	value _v_c,
	value _v_a,
	value _v_to)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int num_exprs; /*in*/
  Z3_ast *to; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _c1 = Wosize_val(_v_to);
  to = camlidl_malloc(_c1 * sizeof(Z3_ast ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_to, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &to[_c2], _ctx);
  }
  num_exprs = _c1;
  _res = Z3_substitute_vars(c, a, num_exprs, to);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_sort_to_ast(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_sort s; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s, &s, _ctx);
  _res = Z3_sort_to_ast(c, s);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_func_decl_to_ast(
	value _v_c,
	value _v_f)
{
  Z3_context c; /*in*/
  Z3_func_decl f; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_f, &f, _ctx);
  _res = Z3_func_decl_to_ast(c, f);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_pattern_to_ast(
	value _v_c,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_pattern p; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_pattern(_v_p, &p, _ctx);
  _res = Z3_pattern_to_ast(c, p);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_app_to_ast(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_app a; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_app(_v_a, &a, _ctx);
  _res = Z3_app_to_ast(c, a);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_to_app(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  Z3_app _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_to_app(c, a);
  _vres = camlidl_c2ml_z3_Z3_app(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_push(
	value _v_c)
{
  Z3_context c; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  Z3_push(c);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_pop(
	value _v_c,
	value _v_num_scopes)
{
  Z3_context c; /*in*/
  unsigned int num_scopes; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  num_scopes = Int_val(_v_num_scopes);
  Z3_pop(c, num_scopes);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_get_num_scopes(
	value _v_c)
{
  Z3_context c; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_num_scopes(c);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_persist_ast(
	value _v_c,
	value _v_a,
	value _v_num_scopes)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  unsigned int num_scopes; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  num_scopes = Int_val(_v_num_scopes);
  Z3_persist_ast(c, a, num_scopes);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_assert_cnstr(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  Z3_assert_cnstr(c, a);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_check_and_get_model(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_model *m; /*out*/
  Z3_lbool _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  Z3_model _c1;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  m = &_c1;
  _res = Z3_check_and_get_model(c, m);
  Begin_roots_block(_vres, 2)
    _vres[0] = camlidl_c2ml_z3_Z3_lbool(&_res, _ctx);
    _vres[1] = camlidl_c2ml_z3_Z3_model(&*m, _ctx);
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3_Z3_check(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_lbool _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_check(c);
  _vres = camlidl_c2ml_z3_Z3_lbool(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_check_assumptions(
	value _v_c,
	value _v_assumptions,
	value _v_core_size,
	value _v_core)
{
  Z3_context c; /*in*/
  unsigned int num_assumptions; /*in*/
  Z3_ast *assumptions; /*in*/
  Z3_model *m; /*out*/
  Z3_ast *proof; /*out*/
  unsigned int *core_size; /*in,out*/
  Z3_ast *core; /*in,out*/
  Z3_lbool _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  unsigned int _c4;
  mlsize_t _c5;
  mlsize_t _c6;
  value _v7;
  Z3_model _c8;
  Z3_ast _c9;
  mlsize_t _c10;
  value _v11;
  value _vresult;
  value _vres[5] = { 0, 0, 0, 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_assumptions);
  assumptions = camlidl_malloc(_c1 * sizeof(Z3_ast ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_assumptions, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &assumptions[_c2], _ctx);
  }
  num_assumptions = _c1;
  core_size = &_c4;
  _c4 = Int_val(_v_core_size);
  _c5 = Wosize_val(_v_core);
  core = camlidl_malloc(_c5 * sizeof(Z3_ast ), _ctx);
  for (_c6 = 0; _c6 < _c5; _c6++) {
    _v7 = Field(_v_core, _c6);
    camlidl_ml2c_z3_Z3_ast(_v7, &core[_c6], _ctx);
  }
  num_assumptions = _c5;
  m = &_c8;
  proof = &_c9;
  _res = Z3_check_assumptions(c, num_assumptions, assumptions, m, proof, core_size, core);
  Begin_roots_block(_vres, 5)
    _vres[0] = camlidl_c2ml_z3_Z3_lbool(&_res, _ctx);
    _vres[1] = camlidl_c2ml_z3_Z3_model(&*m, _ctx);
    _vres[2] = camlidl_c2ml_z3_Z3_ast(&*proof, _ctx);
    _vres[3] = Val_int(*core_size);
    _vres[4] = camlidl_alloc(num_assumptions, 0);
    Begin_root(_vres[4])
      for (_c10 = 0; _c10 < num_assumptions; _c10++) {
        _v11 = camlidl_c2ml_z3_Z3_ast(&core[_c10], _ctx);
        modify(&Field(_vres[4], _c10), _v11);
      }
    End_roots()
    _vresult = camlidl_alloc_small(5, 0);
    { mlsize_t _c12;
      for (_c12 = 0; _c12 < 5; _c12++) Field(_vresult, _c12) = _vres[_c12];
    }
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3_Z3_get_implied_equalities(
	value _v_c,
	value _v_terms)
{
  Z3_context c; /*in*/
  unsigned int num_terms; /*in*/
  Z3_ast *terms; /*in*/
  unsigned int *class_ids; /*out*/
  Z3_lbool _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  value _v5;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _c1 = Wosize_val(_v_terms);
  terms = camlidl_malloc(_c1 * sizeof(Z3_ast ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_terms, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &terms[_c2], _ctx);
  }
  num_terms = _c1;
  class_ids = camlidl_malloc(num_terms * sizeof(unsigned int ), _ctx);
  _res = Z3_get_implied_equalities(c, num_terms, terms, class_ids);
  Begin_roots_block(_vres, 2)
    _vres[0] = camlidl_c2ml_z3_Z3_lbool(&_res, _ctx);
    _vres[1] = camlidl_alloc(num_terms, 0);
    for (_c4 = 0; _c4 < num_terms; _c4++) {
      _v5 = Val_int(class_ids[_c4]);
      modify(&Field(_vres[1], _c4), _v5);
    }
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3_Z3_del_model(
	value _v_c,
	value _v_m)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  Z3_del_model(c, m);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_soft_check_cancel(
	value _v_c)
{
  Z3_context c; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  Z3_soft_check_cancel(c);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_get_search_failure(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_search_failure _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_search_failure(c);
  _vres = camlidl_c2ml_z3_Z3_search_failure(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_relevant_labels(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_literals _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_relevant_labels(c);
  _vres = camlidl_c2ml_z3_Z3_literals(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_relevant_literals(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_literals _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_relevant_literals(c);
  _vres = camlidl_c2ml_z3_Z3_literals(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_guessed_literals(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_literals _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_guessed_literals(c);
  _vres = camlidl_c2ml_z3_Z3_literals(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_del_literals(
	value _v_c,
	value _v_lbls)
{
  Z3_context c; /*in*/
  Z3_literals lbls; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_literals(_v_lbls, &lbls, _ctx);
  Z3_del_literals(c, lbls);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_get_num_literals(
	value _v_c,
	value _v_lbls)
{
  Z3_context c; /*in*/
  Z3_literals lbls; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_literals(_v_lbls, &lbls, _ctx);
  _res = Z3_get_num_literals(c, lbls);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_label_symbol(
	value _v_c,
	value _v_lbls,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_literals lbls; /*in*/
  unsigned int idx; /*in*/
  Z3_symbol _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_literals(_v_lbls, &lbls, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_label_symbol(c, lbls, idx);
  _vres = camlidl_c2ml_z3_Z3_symbol(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_literal(
	value _v_c,
	value _v_lbls,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_literals lbls; /*in*/
  unsigned int idx; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_literals(_v_lbls, &lbls, _ctx);
  idx = Int_val(_v_idx);
  _res = Z3_get_literal(c, lbls, idx);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_disable_literal(
	value _v_c,
	value _v_lbls,
	value _v_idx)
{
  Z3_context c; /*in*/
  Z3_literals lbls; /*in*/
  unsigned int idx; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_literals(_v_lbls, &lbls, _ctx);
  idx = Int_val(_v_idx);
  Z3_disable_literal(c, lbls, idx);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_block_literals(
	value _v_c,
	value _v_lbls)
{
  Z3_context c; /*in*/
  Z3_literals lbls; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_literals(_v_lbls, &lbls, _ctx);
  Z3_block_literals(c, lbls);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_get_model_num_constants(
	value _v_c,
	value _v_m)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  _res = Z3_get_model_num_constants(c, m);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_model_constant(
	value _v_c,
	value _v_m,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int i; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_model_constant(c, m, i);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_eval_func_decl(
	value _v_c,
	value _v_m,
	value _v_decl)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  Z3_func_decl decl; /*in*/
  Z3_ast *v; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  Z3_ast _c1;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_decl, &decl, _ctx);
  v = &_c1;
  _res = Z3_eval_func_decl(c, m, decl, v);
  Begin_roots_block(_vres, 2)
    _vres[0] = Val_int(_res);
    _vres[1] = camlidl_c2ml_z3_Z3_ast(&*v, _ctx);
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3_Z3_is_array_value(
	value _v_c,
	value _v_m,
	value _v_v)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  Z3_ast v; /*in*/
  unsigned int *num_entries; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  unsigned int _c1;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_v, &v, _ctx);
  num_entries = &_c1;
  _res = Z3_is_array_value(c, m, v, num_entries);
  Begin_roots_block(_vres, 2)
    _vres[0] = Val_int(_res);
    _vres[1] = Val_int(*num_entries);
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3_Z3_get_array_value(
	value _v_c,
	value _v_m,
	value _v_v,
	value _v_indices,
	value _v_values)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  Z3_ast v; /*in*/
  unsigned int num_entries; /*in*/
  Z3_ast *indices; /*in,out*/
  Z3_ast *values; /*in,out*/
  Z3_ast *else_value; /*out*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  Z3_ast _c7;
  mlsize_t _c8;
  value _v9;
  mlsize_t _c10;
  value _v11;
  value _vresult;
  value _vres[3] = { 0, 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_v, &v, _ctx);
  _c1 = Wosize_val(_v_indices);
  indices = camlidl_malloc(_c1 * sizeof(Z3_ast ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_indices, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &indices[_c2], _ctx);
  }
  num_entries = _c1;
  _c4 = Wosize_val(_v_values);
  values = camlidl_malloc(_c4 * sizeof(Z3_ast ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_values, _c5);
    camlidl_ml2c_z3_Z3_ast(_v6, &values[_c5], _ctx);
  }
  num_entries = _c4;
  else_value = &_c7;
  Z3_get_array_value(c, m, v, num_entries, indices, values, else_value);
  Begin_roots_block(_vres, 3)
    _vres[0] = camlidl_alloc(num_entries, 0);
    Begin_root(_vres[0])
      for (_c8 = 0; _c8 < num_entries; _c8++) {
        _v9 = camlidl_c2ml_z3_Z3_ast(&indices[_c8], _ctx);
        modify(&Field(_vres[0], _c8), _v9);
      }
    End_roots()
    _vres[1] = camlidl_alloc(num_entries, 0);
    Begin_root(_vres[1])
      for (_c10 = 0; _c10 < num_entries; _c10++) {
        _v11 = camlidl_c2ml_z3_Z3_ast(&values[_c10], _ctx);
        modify(&Field(_vres[1], _c10), _v11);
      }
    End_roots()
    _vres[2] = camlidl_c2ml_z3_Z3_ast(&*else_value, _ctx);
    _vresult = camlidl_alloc_small(3, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3_Z3_get_model_num_funcs(
	value _v_c,
	value _v_m)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  _res = Z3_get_model_num_funcs(c, m);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_model_func_decl(
	value _v_c,
	value _v_m,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int i; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_model_func_decl(c, m, i);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_model_func_else(
	value _v_c,
	value _v_m,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_model_func_else(c, m, i);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_model_func_num_entries(
	value _v_c,
	value _v_m,
	value _v_i)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int i; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_model_func_num_entries(c, m, i);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_model_func_entry_num_args(
	value _v_c,
	value _v_m,
	value _v_i,
	value _v_j)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int i; /*in*/
  unsigned int j; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  i = Int_val(_v_i);
  j = Int_val(_v_j);
  _res = Z3_get_model_func_entry_num_args(c, m, i, j);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_model_func_entry_arg(
	value _v_c,
	value _v_m,
	value _v_i,
	value _v_j,
	value _v_k)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int i; /*in*/
  unsigned int j; /*in*/
  unsigned int k; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  i = Int_val(_v_i);
  j = Int_val(_v_j);
  k = Int_val(_v_k);
  _res = Z3_get_model_func_entry_arg(c, m, i, j, k);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_model_func_entry_value(
	value _v_c,
	value _v_m,
	value _v_i,
	value _v_j)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  unsigned int i; /*in*/
  unsigned int j; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  i = Int_val(_v_i);
  j = Int_val(_v_j);
  _res = Z3_get_model_func_entry_value(c, m, i, j);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_eval(
	value _v_c,
	value _v_m,
	value _v_t)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  Z3_ast t; /*in*/
  Z3_ast *v; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  Z3_ast _c1;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_t, &t, _ctx);
  v = &_c1;
  _res = Z3_eval(c, m, t, v);
  Begin_roots_block(_vres, 2)
    _vres[0] = Val_int(_res);
    _vres[1] = camlidl_c2ml_z3_Z3_ast(&*v, _ctx);
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3_Z3_eval_decl(
	value _v_c,
	value _v_m,
	value _v_d,
	value _v_args)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  Z3_func_decl d; /*in*/
  unsigned int num_args; /*in*/
  Z3_ast *args; /*in*/
  Z3_ast *v; /*out*/
  int _res;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  Z3_ast _c4;
  value _vresult;
  value _vres[2] = { 0, 0, };

  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  _c1 = Wosize_val(_v_args);
  args = camlidl_malloc(_c1 * sizeof(Z3_ast ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_args, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &args[_c2], _ctx);
  }
  num_args = _c1;
  v = &_c4;
  _res = Z3_eval_decl(c, m, d, num_args, args, v);
  Begin_roots_block(_vres, 2)
    _vres[0] = Val_int(_res);
    _vres[1] = camlidl_c2ml_z3_Z3_ast(&*v, _ctx);
    _vresult = camlidl_alloc_small(2, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
  End_roots()
  camlidl_free(_ctx);
  return _vresult;
}

value camlidl_z3_Z3_open_log(
	value _v_c,
	value _v_filename)
{
  Z3_context c; /*in*/
  char const *filename; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  filename = String_val(_v_filename);
  _res = Z3_open_log(c, filename);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_append_log(
	value _v_c,
	value _v_string)
{
  Z3_context c; /*in*/
  char const *string; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  string = String_val(_v_string);
  Z3_append_log(c, string);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_close_log(
	value _v_c)
{
  Z3_context c; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  Z3_close_log(c);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_set_ast_print_mode(
	value _v_c,
	value _v_mode)
{
  Z3_context c; /*in*/
  Z3_ast_print_mode mode; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast_print_mode(_v_mode, &mode, _ctx);
  Z3_set_ast_print_mode(c, mode);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_ast_to_string(
	value _v_c,
	value _v_a)
{
  Z3_context c; /*in*/
  Z3_ast a; /*in*/
  char const *_res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_a, &a, _ctx);
  _res = Z3_ast_to_string(c, a);
  _vres = copy_string(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_pattern_to_string(
	value _v_c,
	value _v_p)
{
  Z3_context c; /*in*/
  Z3_pattern p; /*in*/
  char const *_res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_pattern(_v_p, &p, _ctx);
  _res = Z3_pattern_to_string(c, p);
  _vres = copy_string(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_sort_to_string(
	value _v_c,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_sort s; /*in*/
  char const *_res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s, &s, _ctx);
  _res = Z3_sort_to_string(c, s);
  _vres = copy_string(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_func_decl_to_string(
	value _v_c,
	value _v_d)
{
  Z3_context c; /*in*/
  Z3_func_decl d; /*in*/
  char const *_res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_func_decl_to_string(c, d);
  _vres = copy_string(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_model_to_string(
	value _v_c,
	value _v_m)
{
  Z3_context c; /*in*/
  Z3_model m; /*in*/
  char const *_res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_model(_v_m, &m, _ctx);
  _res = Z3_model_to_string(c, m);
  _vres = copy_string(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_benchmark_to_smtlib_string(
	value _v_c,
	value _v_name,
	value _v_logic,
	value _v_status,
	value _v_attributes,
	value _v_assumptions,
	value _v_formula)
{
  Z3_context c; /*in*/
  char const *name; /*in*/
  char const *logic; /*in*/
  char const *status; /*in*/
  char const *attributes; /*in*/
  unsigned int num_assumptions; /*in*/
  Z3_ast *assumptions; /*in*/
  Z3_ast formula; /*in*/
  char const *_res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  name = String_val(_v_name);
  logic = String_val(_v_logic);
  status = String_val(_v_status);
  attributes = String_val(_v_attributes);
  _c1 = Wosize_val(_v_assumptions);
  assumptions = camlidl_malloc(_c1 * sizeof(Z3_ast ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_assumptions, _c2);
    camlidl_ml2c_z3_Z3_ast(_v3, &assumptions[_c2], _ctx);
  }
  num_assumptions = _c1;
  camlidl_ml2c_z3_Z3_ast(_v_formula, &formula, _ctx);
  _res = Z3_benchmark_to_smtlib_string(c, name, logic, status, attributes, num_assumptions, assumptions, formula);
  _vres = copy_string(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_benchmark_to_smtlib_string_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_benchmark_to_smtlib_string(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6]);
}

value camlidl_z3_Z3_context_to_string(
	value _v_c)
{
  Z3_context c; /*in*/
  char const *_res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_context_to_string(c);
  _vres = copy_string(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_statistics_to_string(
	value _v_c)
{
  Z3_context c; /*in*/
  char const *_res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_statistics_to_string(c);
  _vres = copy_string(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_context_assignment(
	value _v_c)
{
  Z3_context c; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_context_assignment(c);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_parse_smtlib_string(
	value _v_c,
	value _v_str,
	value _v_sort_names,
	value _v_sorts,
	value _v_decl_names,
	value _v_decls)
{
  Z3_context c; /*in*/
  char const *str; /*in*/
  unsigned int num_sorts; /*in*/
  Z3_symbol *sort_names; /*in*/
  Z3_sort *sorts; /*in*/
  unsigned int num_decls; /*in*/
  Z3_symbol *decl_names; /*in*/
  Z3_func_decl *decls; /*in*/
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  mlsize_t _c10;
  mlsize_t _c11;
  value _v12;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  str = String_val(_v_str);
  _c1 = Wosize_val(_v_sort_names);
  sort_names = camlidl_malloc(_c1 * sizeof(Z3_symbol ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_sort_names, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &sort_names[_c2], _ctx);
  }
  num_sorts = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_sorts = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  _c10 = Wosize_val(_v_decls);
  decls = camlidl_malloc(_c10 * sizeof(Z3_func_decl ), _ctx);
  for (_c11 = 0; _c11 < _c10; _c11++) {
    _v12 = Field(_v_decls, _c11);
    camlidl_ml2c_z3_Z3_func_decl(_v12, &decls[_c11], _ctx);
  }
  num_decls = _c10;
  Z3_parse_smtlib_string(c, str, num_sorts, sort_names, sorts, num_decls, decl_names, decls);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_parse_smtlib_string_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_parse_smtlib_string(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3_Z3_parse_smtlib_file(
	value _v_c,
	value _v_file_name,
	value _v_sort_names,
	value _v_sorts,
	value _v_decl_names,
	value _v_decls)
{
  Z3_context c; /*in*/
  char const *file_name; /*in*/
  unsigned int num_sorts; /*in*/
  Z3_symbol *sort_names; /*in*/
  Z3_sort *sorts; /*in*/
  unsigned int num_decls; /*in*/
  Z3_symbol *decl_names; /*in*/
  Z3_func_decl *decls; /*in*/
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  mlsize_t _c10;
  mlsize_t _c11;
  value _v12;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  file_name = String_val(_v_file_name);
  _c1 = Wosize_val(_v_sort_names);
  sort_names = camlidl_malloc(_c1 * sizeof(Z3_symbol ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_sort_names, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &sort_names[_c2], _ctx);
  }
  num_sorts = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_sorts = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  _c10 = Wosize_val(_v_decls);
  decls = camlidl_malloc(_c10 * sizeof(Z3_func_decl ), _ctx);
  for (_c11 = 0; _c11 < _c10; _c11++) {
    _v12 = Field(_v_decls, _c11);
    camlidl_ml2c_z3_Z3_func_decl(_v12, &decls[_c11], _ctx);
  }
  num_decls = _c10;
  Z3_parse_smtlib_file(c, file_name, num_sorts, sort_names, sorts, num_decls, decl_names, decls);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_parse_smtlib_file_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_parse_smtlib_file(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3_Z3_get_smtlib_num_formulas(
	value _v_c)
{
  Z3_context c; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_smtlib_num_formulas(c);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_smtlib_formula(
	value _v_c,
	value _v_i)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_smtlib_formula(c, i);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_smtlib_num_assumptions(
	value _v_c)
{
  Z3_context c; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_smtlib_num_assumptions(c);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_smtlib_assumption(
	value _v_c,
	value _v_i)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_smtlib_assumption(c, i);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_smtlib_num_decls(
	value _v_c)
{
  Z3_context c; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_smtlib_num_decls(c);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_smtlib_decl(
	value _v_c,
	value _v_i)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_func_decl _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_smtlib_decl(c, i);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_smtlib_num_sorts(
	value _v_c)
{
  Z3_context c; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_smtlib_num_sorts(c);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_smtlib_sort(
	value _v_c,
	value _v_i)
{
  Z3_context c; /*in*/
  unsigned int i; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  i = Int_val(_v_i);
  _res = Z3_get_smtlib_sort(c, i);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_get_smtlib_error(
	value _v_c)
{
  Z3_context c; /*in*/
  char const *_res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  _res = Z3_get_smtlib_error(c);
  _vres = copy_string(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_parse_z3_string(
	value _v_c,
	value _v_str)
{
  Z3_context c; /*in*/
  char const *str; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  str = String_val(_v_str);
  _res = Z3_parse_z3_string(c, str);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_parse_z3_file(
	value _v_c,
	value _v_file_name)
{
  Z3_context c; /*in*/
  char const *file_name; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  file_name = String_val(_v_file_name);
  _res = Z3_parse_z3_file(c, file_name);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_parse_smtlib2_string(
	value _v_c,
	value _v_str,
	value _v_sort_names,
	value _v_sorts,
	value _v_decl_names,
	value _v_decls)
{
  Z3_context c; /*in*/
  char const *str; /*in*/
  unsigned int num_sorts; /*in*/
  Z3_symbol *sort_names; /*in*/
  Z3_sort *sorts; /*in*/
  unsigned int num_decls; /*in*/
  Z3_symbol *decl_names; /*in*/
  Z3_func_decl *decls; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  mlsize_t _c10;
  mlsize_t _c11;
  value _v12;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  str = String_val(_v_str);
  _c1 = Wosize_val(_v_sort_names);
  sort_names = camlidl_malloc(_c1 * sizeof(Z3_symbol ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_sort_names, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &sort_names[_c2], _ctx);
  }
  num_sorts = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_sorts = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  _c10 = Wosize_val(_v_decls);
  decls = camlidl_malloc(_c10 * sizeof(Z3_func_decl ), _ctx);
  for (_c11 = 0; _c11 < _c10; _c11++) {
    _v12 = Field(_v_decls, _c11);
    camlidl_ml2c_z3_Z3_func_decl(_v12, &decls[_c11], _ctx);
  }
  num_decls = _c10;
  _res = Z3_parse_smtlib2_string(c, str, num_sorts, sort_names, sorts, num_decls, decl_names, decls);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_parse_smtlib2_string_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_parse_smtlib2_string(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3_Z3_parse_smtlib2_file(
	value _v_c,
	value _v_file_name,
	value _v_sort_names,
	value _v_sorts,
	value _v_decl_names,
	value _v_decls)
{
  Z3_context c; /*in*/
  char const *file_name; /*in*/
  unsigned int num_sorts; /*in*/
  Z3_symbol *sort_names; /*in*/
  Z3_sort *sorts; /*in*/
  unsigned int num_decls; /*in*/
  Z3_symbol *decl_names; /*in*/
  Z3_func_decl *decls; /*in*/
  Z3_ast _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  mlsize_t _c10;
  mlsize_t _c11;
  value _v12;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  file_name = String_val(_v_file_name);
  _c1 = Wosize_val(_v_sort_names);
  sort_names = camlidl_malloc(_c1 * sizeof(Z3_symbol ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_sort_names, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &sort_names[_c2], _ctx);
  }
  num_sorts = _c1;
  _c4 = Wosize_val(_v_sorts);
  sorts = camlidl_malloc(_c4 * sizeof(Z3_sort ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sorts, _c5);
    camlidl_ml2c_z3_Z3_sort(_v6, &sorts[_c5], _ctx);
  }
  num_sorts = _c4;
  _c7 = Wosize_val(_v_decl_names);
  decl_names = camlidl_malloc(_c7 * sizeof(Z3_symbol ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_decl_names, _c8);
    camlidl_ml2c_z3_Z3_symbol(_v9, &decl_names[_c8], _ctx);
  }
  num_decls = _c7;
  _c10 = Wosize_val(_v_decls);
  decls = camlidl_malloc(_c10 * sizeof(Z3_func_decl ), _ctx);
  for (_c11 = 0; _c11 < _c10; _c11++) {
    _v12 = Field(_v_decls, _c11);
    camlidl_ml2c_z3_Z3_func_decl(_v12, &decls[_c11], _ctx);
  }
  num_decls = _c10;
  _res = Z3_parse_smtlib2_file(c, file_name, num_sorts, sort_names, sorts, num_decls, decl_names, decls);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_parse_smtlib2_file_bytecode(value * argv, int argn)
{
  return camlidl_z3_Z3_parse_smtlib2_file(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

value camlidl_z3_Z3_get_version(value _unit)
{
  unsigned int *major; /*out*/
  unsigned int *minor; /*out*/
  unsigned int *build_number; /*out*/
  unsigned int *revision_number; /*out*/
  unsigned int _c1;
  unsigned int _c2;
  unsigned int _c3;
  unsigned int _c4;
  value _vresult;
  value _vres[4] = { 0, 0, 0, 0, };

  major = &_c1;
  minor = &_c2;
  build_number = &_c3;
  revision_number = &_c4;
  Z3_get_version(major, minor, build_number, revision_number);
  Begin_roots_block(_vres, 4)
    _vres[0] = Val_int(*major);
    _vres[1] = Val_int(*minor);
    _vres[2] = Val_int(*build_number);
    _vres[3] = Val_int(*revision_number);
    _vresult = camlidl_alloc_small(4, 0);
    Field(_vresult, 0) = _vres[0];
    Field(_vresult, 1) = _vres[1];
    Field(_vresult, 2) = _vres[2];
    Field(_vresult, 3) = _vres[3];
  End_roots()
  return _vresult;
}

value camlidl_z3_Z3_reset_memory(value _unit)
{
  Z3_reset_memory();
  return Val_unit;
}

value camlidl_z3_Z3_theory_mk_sort(
	value _v_c,
	value _v_t,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_theory t; /*in*/
  Z3_symbol s; /*in*/
  Z3_sort _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_s, &s, _ctx);
  _res = Z3_theory_mk_sort(c, t, s);
  _vres = camlidl_c2ml_z3_Z3_sort(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_theory_mk_value(
	value _v_c,
	value _v_t,
	value _v_n,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_theory t; /*in*/
  Z3_symbol n; /*in*/
  Z3_sort s; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_n, &n, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s, &s, _ctx);
  _res = Z3_theory_mk_value(c, t, n, s);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_theory_mk_constant(
	value _v_c,
	value _v_t,
	value _v_n,
	value _v_s)
{
  Z3_context c; /*in*/
  Z3_theory t; /*in*/
  Z3_symbol n; /*in*/
  Z3_sort s; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_n, &n, _ctx);
  camlidl_ml2c_z3_Z3_sort(_v_s, &s, _ctx);
  _res = Z3_theory_mk_constant(c, t, n, s);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_theory_mk_func_decl(
	value _v_c,
	value _v_t,
	value _v_n,
	value _v_domain,
	value _v_range)
{
  Z3_context c; /*in*/
  Z3_theory t; /*in*/
  Z3_symbol n; /*in*/
  unsigned int domain_size; /*in*/
  Z3_sort const *domain; /*in*/
  Z3_sort range; /*in*/
  Z3_func_decl _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_n, &n, _ctx);
  _c1 = Wosize_val(_v_domain);
  domain = camlidl_malloc(_c1 * sizeof(Z3_sort const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_domain, _c2);
    camlidl_ml2c_z3_Z3_sort(_v3, &domain[_c2], _ctx);
  }
  domain_size = _c1;
  camlidl_ml2c_z3_Z3_sort(_v_range, &range, _ctx);
  _res = Z3_theory_mk_func_decl(c, t, n, domain_size, domain, range);
  _vres = camlidl_c2ml_z3_Z3_func_decl(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_theory_get_context(
	value _v_t)
{
  Z3_theory t; /*in*/
  Z3_context _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  _res = Z3_theory_get_context(t);
  _vres = camlidl_c2ml_z3_Z3_context(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_theory_assert_axiom(
	value _v_t,
	value _v_ax)
{
  Z3_theory t; /*in*/
  Z3_ast ax; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_ax, &ax, _ctx);
  Z3_theory_assert_axiom(t, ax);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_theory_assume_eq(
	value _v_t,
	value _v_lhs,
	value _v_rhs)
{
  Z3_theory t; /*in*/
  Z3_ast lhs; /*in*/
  Z3_ast rhs; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_lhs, &lhs, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_rhs, &rhs, _ctx);
  Z3_theory_assume_eq(t, lhs, rhs);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_theory_enable_axiom_simplification(
	value _v_t,
	value _v_flag)
{
  Z3_theory t; /*in*/
  int flag; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  flag = Int_val(_v_flag);
  Z3_theory_enable_axiom_simplification(t, flag);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_theory_get_eqc_root(
	value _v_t,
	value _v_n)
{
  Z3_theory t; /*in*/
  Z3_ast n; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_n, &n, _ctx);
  _res = Z3_theory_get_eqc_root(t, n);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_theory_get_eqc_next(
	value _v_t,
	value _v_n)
{
  Z3_theory t; /*in*/
  Z3_ast n; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_n, &n, _ctx);
  _res = Z3_theory_get_eqc_next(t, n);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_theory_get_num_parents(
	value _v_t,
	value _v_n)
{
  Z3_theory t; /*in*/
  Z3_ast n; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_n, &n, _ctx);
  _res = Z3_theory_get_num_parents(t, n);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_theory_get_parent(
	value _v_t,
	value _v_n,
	value _v_i)
{
  Z3_theory t; /*in*/
  Z3_ast n; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_n, &n, _ctx);
  i = Int_val(_v_i);
  _res = Z3_theory_get_parent(t, n, i);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_theory_is_value(
	value _v_t,
	value _v_n)
{
  Z3_theory t; /*in*/
  Z3_ast n; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_n, &n, _ctx);
  _res = Z3_theory_is_value(t, n);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_theory_is_decl(
	value _v_t,
	value _v_d)
{
  Z3_theory t; /*in*/
  Z3_func_decl d; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_d, &d, _ctx);
  _res = Z3_theory_is_decl(t, d);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_theory_get_num_elems(
	value _v_t)
{
  Z3_theory t; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  _res = Z3_theory_get_num_elems(t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_theory_get_elem(
	value _v_t,
	value _v_i)
{
  Z3_theory t; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  i = Int_val(_v_i);
  _res = Z3_theory_get_elem(t, i);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_theory_get_num_apps(
	value _v_t)
{
  Z3_theory t; /*in*/
  unsigned int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  _res = Z3_theory_get_num_apps(t);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_theory_get_app(
	value _v_t,
	value _v_i)
{
  Z3_theory t; /*in*/
  unsigned int i; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_theory(_v_t, &t, _ctx);
  i = Int_val(_v_i);
  _res = Z3_theory_get_app(t, i);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_datalog_add_rule(
	value _v_c,
	value _v_horn_rule,
	value _v_name)
{
  Z3_context c; /*in*/
  Z3_ast horn_rule; /*in*/
  Z3_symbol name; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_horn_rule, &horn_rule, _ctx);
  camlidl_ml2c_z3_Z3_symbol(_v_name, &name, _ctx);
  Z3_datalog_add_rule(c, horn_rule, name);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_datalog_query(
	value _v_c,
	value _v_q)
{
  Z3_context c; /*in*/
  Z3_ast q; /*in*/
  Z3_ast _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_ast(_v_q, &q, _ctx);
  _res = Z3_datalog_query(c, q);
  _vres = camlidl_c2ml_z3_Z3_ast(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_z3_Z3_datalog_set_predicate_representation(
	value _v_c,
	value _v_f,
	value _v_relation_kinds)
{
  Z3_context c; /*in*/
  Z3_func_decl f; /*in*/
  unsigned int num_relations; /*in*/
  Z3_symbol const *relation_kinds; /*in*/
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  camlidl_ml2c_z3_Z3_func_decl(_v_f, &f, _ctx);
  _c1 = Wosize_val(_v_relation_kinds);
  relation_kinds = camlidl_malloc(_c1 * sizeof(Z3_symbol const ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_relation_kinds, _c2);
    camlidl_ml2c_z3_Z3_symbol(_v3, &relation_kinds[_c2], _ctx);
  }
  num_relations = _c1;
  Z3_datalog_set_predicate_representation(c, f, num_relations, relation_kinds);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_z3_Z3_datalog_parse_file(
	value _v_c,
	value _v_filename)
{
  Z3_context c; /*in*/
  char const *filename; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_z3_Z3_context(_v_c, &c, _ctx);
  filename = String_val(_v_filename);
  Z3_datalog_parse_file(c, filename);
  camlidl_free(_ctx);
  return Val_unit;
}

