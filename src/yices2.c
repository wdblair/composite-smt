/* -*- C -*-
 *
 * SMT-LIB v2 interface to Yices 1
 *
 * Author: Alberto Griggio <griggio@fbk.eu>
 *
 * Copyright (C) 2010 Alberto Griggio
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

/*
  Ported to Yices 2 by Will Blair and Nikka Ghalili
 */

#include "parser/smtlib2yices.h"
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#define KEEP_SUBS 1

static void smtlib2_yices_parser_set_logic(smtlib2_parser_interface *p,
                                           const char *logic);
static void smtlib2_yices_parser_declare_sort(smtlib2_parser_interface *p,
                                              const char *sortname,
                                              int arity);
static void smtlib2_yices_parser_define_sort(smtlib2_parser_interface *p,
                                             const char *sortname,
                                             smtlib2_vector *params,
                                             smtlib2_sort sort);
static void smtlib2_yices_parser_declare_function(smtlib2_parser_interface *p,
                                                  const char *name,
                                                  smtlib2_sort sort);
static void smtlib2_yices_parser_define_function(smtlib2_parser_interface *p,
                                                 const char *name,
                                                 smtlib2_vector *params,
                                                 smtlib2_sort sort,
                                                 smtlib2_term term);
static smtlib2_sort smtlib2_yices_parser_make_sort(smtlib2_parser_interface *p,
                                                   const char *sortname,
                                                   smtlib2_vector *index);
static smtlib2_sort smtlib2_yices_parser_make_function_sort(
                                                    smtlib2_parser_interface *p,
                                                    smtlib2_vector *tps);
static smtlib2_sort smtlib2_yices_parser_make_parametric_sort(
                                                    smtlib2_parser_interface *p,
                                                    const char *name,
                                                    smtlib2_vector *tps);

static void smtlib2_yices_parser_push(smtlib2_parser_interface *p, int n);
static void smtlib2_yices_parser_pop(smtlib2_parser_interface *p, int n);
static void smtlib2_yices_parser_assert_formula(smtlib2_parser_interface *p,
                                                smtlib2_term term);
static void smtlib2_yices_parser_check_sat(smtlib2_parser_interface *p);

static void smtlib2_yices_parser_annotate_term(smtlib2_parser_interface *p,
                                               smtlib2_term term,
                                               smtlib2_vector *annotations);
static void smtlib2_yices_parser_set_int_option(smtlib2_parser_interface *p,
                                                const char *keyword,
                                                int value);
static void smtlib2_yices_parser_get_assignment(smtlib2_parser_interface *p);
static void smtlib2_yices_parser_get_value(smtlib2_parser_interface *p,
                                           smtlib2_vector *terms);
static void smtlib2_yices_parser_get_unsat_core(smtlib2_parser_interface *p);

static smtlib2_term smtlib2_yices_parser_mk_function(smtlib2_context ctx,
                                                     const char *symbol,
                                                     smtlib2_sort sort,
                                                     smtlib2_vector *index,
                                                     smtlib2_vector *args);
static smtlib2_term smtlib2_yices_parser_mk_number(smtlib2_context ctx,
                                                   const char *rep,
                                                   unsigned int width,
                                                   unsigned int base);

smtlib2_sort smtlib2_yices_new_type (type_t t) {
  type_t *sort = malloc(sizeof(type_t));
  
  assert(sort != NULL);
  
  *sort = t;
  return sort;
}

#define SMTLIB2_YICES_DECLHANDLER(name)                                 \
    static smtlib2_term smtlib2_yices_parser_mk_ ## name (              \
        smtlib2_context ctx,                                            \
        const char *symbol,                                             \
        smtlib2_sort sort,                                              \
        smtlib2_vector *idx,                                            \
        smtlib2_vector *args)

SMTLIB2_YICES_DECLHANDLER(and);
SMTLIB2_YICES_DECLHANDLER(or);
SMTLIB2_YICES_DECLHANDLER(not);
SMTLIB2_YICES_DECLHANDLER(implies);
SMTLIB2_YICES_DECLHANDLER(eq);
SMTLIB2_YICES_DECLHANDLER(plus);
SMTLIB2_YICES_DECLHANDLER(times);
SMTLIB2_YICES_DECLHANDLER(minus);
SMTLIB2_YICES_DECLHANDLER(leq);
SMTLIB2_YICES_DECLHANDLER(lt);
SMTLIB2_YICES_DECLHANDLER(geq);
SMTLIB2_YICES_DECLHANDLER(gt);
SMTLIB2_YICES_DECLHANDLER(ite);
SMTLIB2_YICES_DECLHANDLER(divide);
SMTLIB2_YICES_DECLHANDLER(distinct);
SMTLIB2_YICES_DECLHANDLER(xor);
SMTLIB2_YICES_DECLHANDLER(nand);
SMTLIB2_YICES_DECLHANDLER(to_real);

SMTLIB2_YICES_DECLHANDLER(concat);
SMTLIB2_YICES_DECLHANDLER(bvnot);
SMTLIB2_YICES_DECLHANDLER(bvand);
SMTLIB2_YICES_DECLHANDLER(bvnand);
SMTLIB2_YICES_DECLHANDLER(bvor);
SMTLIB2_YICES_DECLHANDLER(bvnor);
SMTLIB2_YICES_DECLHANDLER(bvxor);
SMTLIB2_YICES_DECLHANDLER(bvxnor);
SMTLIB2_YICES_DECLHANDLER(bvult);
SMTLIB2_YICES_DECLHANDLER(bvslt);
SMTLIB2_YICES_DECLHANDLER(bvule);
SMTLIB2_YICES_DECLHANDLER(bvsle);
SMTLIB2_YICES_DECLHANDLER(bvugt);
SMTLIB2_YICES_DECLHANDLER(bvsgt);
SMTLIB2_YICES_DECLHANDLER(bvuge);
SMTLIB2_YICES_DECLHANDLER(bvsge);
SMTLIB2_YICES_DECLHANDLER(bvcomp);
SMTLIB2_YICES_DECLHANDLER(bvneg);
SMTLIB2_YICES_DECLHANDLER(bvadd);
SMTLIB2_YICES_DECLHANDLER(bvsub);
SMTLIB2_YICES_DECLHANDLER(bvmul);
SMTLIB2_YICES_DECLHANDLER(bvudiv);
SMTLIB2_YICES_DECLHANDLER(bvsdiv);
SMTLIB2_YICES_DECLHANDLER(bvsmod);
SMTLIB2_YICES_DECLHANDLER(bvurem);
SMTLIB2_YICES_DECLHANDLER(bvsrem);
SMTLIB2_YICES_DECLHANDLER(bvshl);
SMTLIB2_YICES_DECLHANDLER(bvlshr);
SMTLIB2_YICES_DECLHANDLER(bvashr);
SMTLIB2_YICES_DECLHANDLER(extract);
SMTLIB2_YICES_DECLHANDLER(repeat);
SMTLIB2_YICES_DECLHANDLER(zero_extend);
SMTLIB2_YICES_DECLHANDLER(sign_extend);
SMTLIB2_YICES_DECLHANDLER(rotate_left);
SMTLIB2_YICES_DECLHANDLER(rotate_right);

#define SMTLIB2_YICES_SETHANDLER(tp, s, name)                           \
  smtlib2_term_parser_set_handler(tp, s, smtlib2_yices_parser_mk_ ## name)

typedef struct smtlib2_yices_parametric_sort {
    char *name_;
    smtlib2_vector *params_;
} smtlib2_yices_parametric_sort;

static smtlib2_yices_parametric_sort *smtlib2_yices_parametric_sort_new(
                                         const char *n, smtlib2_vector *params);
static void smtlib2_yices_parametric_sort_delete(
                                              smtlib2_yices_parametric_sort *s);
static uint32_t smtlib2_yices_parametric_sort_hashfun(intptr_t s);
static bool smtlib2_yices_parametric_sort_eqfun(intptr_t s1, intptr_t s2);

smtlib2_yices_parser *smtlib2_yices_parser_new(void)
{
  yices_init();
  
  smtlib2_yices_parser *ret =
    (smtlib2_yices_parser *)malloc(sizeof(smtlib2_yices_parser));
    smtlib2_parser_interface *pi;
    smtlib2_term_parser *tp;
    
    ctx_config_t *conf = yices_new_config();

    assert(conf != NULL);

    yices_set_config(conf, "mode", "push-pop");

    context_t *ctx = yices_new_context(conf);
    
    assert(ctx != NULL);

    ret->ctx_ = ctx;

    yices_free_config(conf);

    smtlib2_abstract_parser_init((smtlib2_abstract_parser *)ret,
                                 (smtlib2_context)ret);
    ret->sorts_ = smtlib2_hashtable_new(smtlib2_yices_parametric_sort_hashfun,
                                        smtlib2_yices_parametric_sort_eqfun);
    ret->parametric_sorts_ = smtlib2_hashtable_new(smtlib2_hashfun_str,
                                                   smtlib2_eqfun_str);
    ret->next_sort_idx_ = 1;
    ret->numbers_ = smtlib2_hashtable_new(NULL, NULL);
    ret->defines_ = smtlib2_vector_new();
    ret->defines_sorts_ = smtlib2_vector_new();
    ret->logics_arith_only_ = smtlib2_hashtable_new(smtlib2_hashfun_str,
                                                    smtlib2_eqfun_str);
    smtlib2_hashtable_set(ret->logics_arith_only_, (intptr_t)"QF_LRA", 1);
    smtlib2_hashtable_set(ret->logics_arith_only_, (intptr_t)"QF_LIA", 1);
    smtlib2_hashtable_set(ret->logics_arith_only_, (intptr_t)"QF_RDL", 1);
    smtlib2_hashtable_set(ret->logics_arith_only_, (intptr_t)"QF_IDL", 1);
    ret->named_terms_ = smtlib2_hashtable_new(smtlib2_hashfun_str,
                                              smtlib2_eqfun_str);
    ret->term_names_ = smtlib2_hashtable_new(NULL, NULL);
    ret->assertion_ids_ = smtlib2_hashtable_new(NULL, NULL);
    ret->names_ = smtlib2_vector_new();

    /* initialize the term parser and override virtual methods */
    pi = SMTLIB2_PARSER_INTERFACE(ret);
    pi->set_logic = smtlib2_yices_parser_set_logic;
    pi->declare_sort = smtlib2_yices_parser_declare_sort;
    pi->declare_function = smtlib2_yices_parser_declare_function;
    pi->define_function = smtlib2_yices_parser_define_function;
    pi->push = smtlib2_yices_parser_push;
    pi->pop = smtlib2_yices_parser_pop;
    pi->assert_formula = smtlib2_yices_parser_assert_formula;
    pi->check_sat = smtlib2_yices_parser_check_sat;
    pi->annotate_term = smtlib2_yices_parser_annotate_term;
    pi->set_int_option = smtlib2_yices_parser_set_int_option;
    pi->get_unsat_core = smtlib2_yices_parser_get_unsat_core;
    pi->get_assignment = smtlib2_yices_parser_get_assignment;
    pi->get_value = smtlib2_yices_parser_get_value;
    pi->make_sort = smtlib2_yices_parser_make_sort;
    pi->make_function_sort = smtlib2_yices_parser_make_function_sort;
    pi->make_parametric_sort = smtlib2_yices_parser_make_parametric_sort;
    pi->define_sort = smtlib2_yices_parser_define_sort;

    tp = ((smtlib2_abstract_parser *)ret)->termparser_;
    smtlib2_term_parser_set_function_handler(tp,
                                             smtlib2_yices_parser_mk_function);
    smtlib2_term_parser_set_number_handler(tp,
                                           smtlib2_yices_parser_mk_number);
    
    SMTLIB2_YICES_SETHANDLER(tp, "and", and);
    SMTLIB2_YICES_SETHANDLER(tp, "or", or);
    SMTLIB2_YICES_SETHANDLER(tp, "not", not);
    SMTLIB2_YICES_SETHANDLER(tp, "=>", implies);
    SMTLIB2_YICES_SETHANDLER(tp, "=", eq);
    SMTLIB2_YICES_SETHANDLER(tp, "+", plus);
    SMTLIB2_YICES_SETHANDLER(tp, "*", times);
    SMTLIB2_YICES_SETHANDLER(tp, "-", minus);
    SMTLIB2_YICES_SETHANDLER(tp, "<=", leq);
    SMTLIB2_YICES_SETHANDLER(tp, "<", lt);
    SMTLIB2_YICES_SETHANDLER(tp, ">=", geq);
    SMTLIB2_YICES_SETHANDLER(tp, ">", gt);
    SMTLIB2_YICES_SETHANDLER(tp, "ite", ite);
    SMTLIB2_YICES_SETHANDLER(tp, "/", divide);
    SMTLIB2_YICES_SETHANDLER(tp, "distinct", distinct);
    SMTLIB2_YICES_SETHANDLER(tp, "xor", xor);
    SMTLIB2_YICES_SETHANDLER(tp, "nand", nand);
    SMTLIB2_YICES_SETHANDLER(tp, "to_real", to_real);

    SMTLIB2_YICES_SETHANDLER(tp, "concat", concat);
    SMTLIB2_YICES_SETHANDLER(tp, "bvnot", bvnot);
    SMTLIB2_YICES_SETHANDLER(tp, "bvand", bvand);
    SMTLIB2_YICES_SETHANDLER(tp, "bvnand", bvnand);
    SMTLIB2_YICES_SETHANDLER(tp, "bvor", bvor);
    SMTLIB2_YICES_SETHANDLER(tp, "bvnor", bvnor);
    SMTLIB2_YICES_SETHANDLER(tp, "bvxor", bvxor);
    SMTLIB2_YICES_SETHANDLER(tp, "bvxnor", bvxnor);
    SMTLIB2_YICES_SETHANDLER(tp, "bvult", bvult);
    SMTLIB2_YICES_SETHANDLER(tp, "bvslt", bvslt);
    SMTLIB2_YICES_SETHANDLER(tp, "bvule", bvule);
    SMTLIB2_YICES_SETHANDLER(tp, "bvsle", bvsle);
    SMTLIB2_YICES_SETHANDLER(tp, "bvugt", bvugt);
    SMTLIB2_YICES_SETHANDLER(tp, "bvsgt", bvsgt);
    SMTLIB2_YICES_SETHANDLER(tp, "bvuge", bvuge);
    SMTLIB2_YICES_SETHANDLER(tp, "bvsge", bvsge);
    SMTLIB2_YICES_SETHANDLER(tp, "bvcomp", bvcomp);
    SMTLIB2_YICES_SETHANDLER(tp, "bvneg", bvneg);
    SMTLIB2_YICES_SETHANDLER(tp, "bvadd", bvadd);
    SMTLIB2_YICES_SETHANDLER(tp, "bvsub", bvsub);
    SMTLIB2_YICES_SETHANDLER(tp, "bvmul", bvmul);
    SMTLIB2_YICES_SETHANDLER(tp, "bvudiv", bvudiv);
    SMTLIB2_YICES_SETHANDLER(tp, "bvsdiv", bvsdiv);
    SMTLIB2_YICES_SETHANDLER(tp, "bvsmod", bvsmod);
    SMTLIB2_YICES_SETHANDLER(tp, "bvurem", bvurem);
    SMTLIB2_YICES_SETHANDLER(tp, "bvsrem", bvsrem);
    SMTLIB2_YICES_SETHANDLER(tp, "bvshl", bvshl);
    SMTLIB2_YICES_SETHANDLER(tp, "bvlshr", bvlshr);
    SMTLIB2_YICES_SETHANDLER(tp, "bvashr", bvashr);
    SMTLIB2_YICES_SETHANDLER(tp, "extract", extract);
    SMTLIB2_YICES_SETHANDLER(tp, "repeat", repeat);
    SMTLIB2_YICES_SETHANDLER(tp, "zero_extend", zero_extend);
    SMTLIB2_YICES_SETHANDLER(tp, "sign_extend", sign_extend);
    SMTLIB2_YICES_SETHANDLER(tp, "rotate_left", rotate_left);
    SMTLIB2_YICES_SETHANDLER(tp, "rotate_right", rotate_right);
    
    /* the built-in sorts */
    smtlib2_hashtable_set(ret->sorts_,
                          (intptr_t)smtlib2_yices_parametric_sort_new(
                                                                      "Bool", NULL),
                          (intptr_t)smtlib2_yices_new_type(yices_bool_type()));
    smtlib2_hashtable_set(ret->sorts_,
                          (intptr_t)smtlib2_yices_parametric_sort_new(
                                                                      "Int", NULL),
                          (intptr_t)smtlib2_yices_new_type(yices_int_type()));
    smtlib2_hashtable_set(ret->sorts_,
                          (intptr_t)smtlib2_yices_parametric_sort_new(
                                                                      "Real", NULL),
                          (intptr_t)smtlib2_yices_new_type(yices_real_type()));

    return ret;
}

#define YCTX(p) (((smtlib2_yices_parser *)(p))->ctx_)

void smtlib2_yices_parser_delete(smtlib2_yices_parser *p)
{
    size_t i;
    smtlib2_vector_delete(p->names_);
    smtlib2_hashtable_delete(p->assertion_ids_, NULL, NULL);
    smtlib2_hashtable_delete(p->named_terms_, (smtlib2_freefun)NULL, NULL);
    smtlib2_hashtable_delete(p->term_names_, NULL, NULL);
    smtlib2_hashtable_delete(p->logics_arith_only_, NULL, NULL);
    smtlib2_vector_delete(p->defines_sorts_);
    for (i = 0; i < smtlib2_vector_size(p->defines_); ++i) {
        char *s = (char *)smtlib2_vector_at(p->defines_, i);
        if (s) free(s);
    }
    smtlib2_vector_delete(p->defines_);
    smtlib2_hashtable_delete(p->numbers_, NULL, (smtlib2_freefun)free);
    smtlib2_hashtable_delete(p->parametric_sorts_, NULL, NULL);
    smtlib2_hashtable_delete(
                             p->sorts_, (smtlib2_freefun)smtlib2_yices_parametric_sort_delete, (smtlib2_freefun)free);
    smtlib2_abstract_parser_deinit(&(p->parent_));
    yices_free_context(p->ctx_);
    free(p);
    yices_exit();
}

static void smtlib2_yices_parser_set_logic(smtlib2_parser_interface *p,
                                           const char *logic)
{
  smtlib2_yices_parser *yp = (smtlib2_yices_parser *)p;
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *)p;
  
  smtlib2_abstract_parser_set_logic(p, logic);
  if (ap->response_ != SMTLIB2_RESPONSE_ERROR) {
    intptr_t v;
    if (smtlib2_hashtable_find(yp->logics_arith_only_,
                               (intptr_t)logic, &v)) {
      
      //add optimization (if there's time)
      //context_t *ctx = YCTX(yp);
      
      //yices_free_context(ctx);
      
      //yices_set_arith_only(true); Delete the context, recreate it for arithmetic only.
    }
  }
}

static void smtlib2_yices_parser_declare_sort(smtlib2_parser_interface *p,
                                              const char *sortname,
                                              int arity)
{
  smtlib2_yices_parser *yp = (smtlib2_yices_parser *)p;
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *)p;
    
    if (ap->response_ != SMTLIB2_RESPONSE_ERROR) {
        term_t tp;
        smtlib2_yices_parametric_sort *n;
        //sprintf(s, "ytp_%d", yp->next_sort_idx_++);
        ap->response_ = SMTLIB2_RESPONSE_SUCCESS;
        tp = yices_new_uninterpreted_type();
        n = smtlib2_yices_parametric_sort_new(sortname, NULL);
        smtlib2_hashtable_set(yp->sorts_, (intptr_t)n, (intptr_t)smtlib2_yices_new_type(tp));
        if (smtlib2_vector_size(yp->defines_sorts_) > 0) {
          smtlib2_vector_push(yp->defines_sorts_, (intptr_t)n);
        }
        if (arity > 0) {
          smtlib2_hashtable_set(yp->parametric_sorts_,
                                (intptr_t)n->name_, (intptr_t)arity);
        }
    }
}

static void smtlib2_yices_parser_define_sort(smtlib2_parser_interface *p,
                                             const char *sortname,
                                             smtlib2_vector *params,
                                             smtlib2_sort sort)
{
  
    smtlib2_yices_parser *yp = (smtlib2_yices_parser *)p;
    smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *)p;
    
    if (ap->response_ != SMTLIB2_RESPONSE_ERROR) {
        if (params != NULL) {
            ap->response_ = SMTLIB2_RESPONSE_ERROR;
            ap->errmsg_ =
                smtlib2_strdup("define-sort with parameters unsupported");
        } else {
            smtlib2_yices_parametric_sort *ps =
                smtlib2_yices_parametric_sort_new(sortname, NULL);
            intptr_t tp;
            if (smtlib2_hashtable_find(yp->sorts_, (intptr_t)ps, &tp)) {
                ap->response_ = SMTLIB2_RESPONSE_ERROR;
                ap->errmsg_ = smtlib2_sprintf(
                    "sort `%s' already declared or defined", sortname);
                smtlib2_yices_parametric_sort_delete(ps);
            } else {
              smtlib2_hashtable_set(yp->sorts_, (intptr_t)ps, (intptr_t)sort);
              if (smtlib2_vector_size(yp->defines_sorts_) > 0) {
                smtlib2_vector_push(yp->defines_sorts_, (intptr_t)ps);
              }
            }
        }
    }
}


static void smtlib2_yices_parser_declare_function(smtlib2_parser_interface *p,
                                                  const char *name,
                                                  smtlib2_sort sort)
{
    smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *)p;
    
    if (ap->response_ != SMTLIB2_RESPONSE_ERROR) {
      
      term_t t = yices_new_uninterpreted_term(*(type_t*)sort);

      assert(t > 0);
      
      int status = yices_set_term_name(t, name);

      if (status == 0) {
        ap->response_ = SMTLIB2_RESPONSE_SUCCESS;
      } else {
        ap->response_ = SMTLIB2_RESPONSE_ERROR;
        ap->errmsg_ = smtlib2_sprintf(
                                      "error declaring function `%s'", name);
      }
    }
}

static void smtlib2_yices_parser_define_function(smtlib2_parser_interface *p,
                                                 const char *name,
                                                 smtlib2_vector *params,
                                                 smtlib2_sort sort,
                                                 smtlib2_term term)
{
    smtlib2_yices_parser *yp = (smtlib2_yices_parser *)p;
    smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *)p;
    
    smtlib2_abstract_parser_define_function(p, name, params, sort, term);
    
    if (ap->response_ != SMTLIB2_RESPONSE_ERROR &&
        smtlib2_vector_size(yp->defines_) > 0) {
        smtlib2_term_parser *tp = ap->termparser_;
        intptr_t k;
        if (smtlib2_hashtable_find_key(tp->bindings_, (intptr_t)name, &k)) {
            smtlib2_vector_push(yp->defines_, k);
        }
    }
}


static smtlib2_sort smtlib2_yices_parser_make_sort(smtlib2_parser_interface *p,
                                                   const char *sortname,
                                                   smtlib2_vector *index)
{
    smtlib2_yices_parser *yp = (smtlib2_yices_parser *)p;
    smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *)p;
    
    if (ap->response_ != SMTLIB2_RESPONSE_ERROR) {
        if (index != NULL) {
            if (strcmp(sortname, "BitVec") == 0 &&
                smtlib2_vector_size(index) == 1) {
                int width = (int)smtlib2_vector_at(index, 0);
                type_t bv = yices_bv_type(width);
                if (bv < 0) {
                    ap->response_ = SMTLIB2_RESPONSE_ERROR;
                    ap->errmsg_ = smtlib2_sprintf(
                        "error creating bit-vector sort of size %d", width);
                }
                return smtlib2_yices_new_type(bv);
            } else {
                ap->response_ = SMTLIB2_RESPONSE_ERROR;
                ap->errmsg_ = smtlib2_sprintf(
                    "unsupported indexed sort `%s', index size %d", sortname,
                    smtlib2_vector_size(index));
                return NULL;
            }
        } else {
            intptr_t v;
            smtlib2_sort ret = NULL;
            smtlib2_yices_parametric_sort tmp = { (char *)sortname, NULL };
            ap->response_ = SMTLIB2_RESPONSE_SUCCESS;
            if (smtlib2_hashtable_find(yp->sorts_, (intptr_t)&tmp, &v)) {
                ret = (smtlib2_sort)v;
            } else {
                ap->response_ = SMTLIB2_RESPONSE_ERROR;
                ap->errmsg_ = smtlib2_sprintf("unknown sort `%s'", sortname);
            }
            return ret;
        }
    } else {
        return NULL;
    }
}


static smtlib2_sort smtlib2_yices_parser_make_function_sort(
                                                    smtlib2_parser_interface *p,
                                                    smtlib2_vector *tps)
{
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *)p;

  smtlib2_sort ret = NULL;
  
  if (ap->response_ != SMTLIB2_RESPONSE_ERROR) {
    type_t *domain;
    type_t range;
    type_t tp;
    unsigned domain_size;
    
    domain_size = smtlib2_vector_size(tps)-1;
    
    domain = malloc(sizeof(type_t)*domain_size);

    assert(domain != NULL);

    for(int i = 0; i < domain_size; i++) {
      domain[i] = *(type_t*)smtlib2_vector_at(tps, i);
    }
    
    range = *(type_t*)smtlib2_vector_last(tps);
    
    tp = yices_function_type(domain_size, domain, range);
    
    assert(tp >= 0);
    
    ret = smtlib2_yices_new_type(tp);


  }
  
  return ret;
}


static smtlib2_sort smtlib2_yices_parser_make_parametric_sort(
    smtlib2_parser_interface *p, const char *name, smtlib2_vector *tps)
{
    smtlib2_yices_parser *yp = (smtlib2_yices_parser *)p;
    smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *)p;

    smtlib2_sort ret = NULL;
    
    if (ap->response_ != SMTLIB2_RESPONSE_ERROR) {
        size_t n1 = smtlib2_vector_size(tps);
        intptr_t n2;

        if (!smtlib2_hashtable_find(yp->parametric_sorts_,
                                    (intptr_t)name, &n2) || n1 != (size_t)n2) {
            ap->response_ = SMTLIB2_RESPONSE_ERROR;
            ap->errmsg_ = smtlib2_sprintf("wrong number of arguments for "
                                          "parametric sort `%s'", name);
        } else {
            smtlib2_yices_parametric_sort tmp = { (char *)name, tps };
            if (smtlib2_hashtable_find(yp->sorts_, (intptr_t)&tmp, &n2)) {
                /* sort already there */
                ret = (smtlib2_sort)n2;
            } else {
                /* create a new instance of this parametric sort */
              term_t tp;
              smtlib2_yices_parametric_sort *ps =
                smtlib2_yices_parametric_sort_new(name, tps);
              tp = yices_new_uninterpreted_type();

              assert(tp >= 0);

              ret = smtlib2_yices_new_type(tp);

              smtlib2_hashtable_set(yp->sorts_, (intptr_t)ps, (intptr_t)ret);
              if (smtlib2_vector_size(yp->defines_sorts_) > 0) {
                smtlib2_vector_push(yp->defines_sorts_, (intptr_t)ps);
              }
            }
        }
    }
    return ret;
}

static void smtlib2_yices_parser_push(smtlib2_parser_interface *p, int n)
{
  smtlib2_yices_parser *yp = (smtlib2_yices_parser *)p;
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *)p;

    if (ap->response_ != SMTLIB2_RESPONSE_ERROR) {
        while (n-- > 0) {
          smtlib2_vector_push(yp->defines_, (intptr_t)NULL);
          smtlib2_vector_push(yp->defines_sorts_, (intptr_t)NULL);
          smtlib2_vector_push(yp->names_, (intptr_t)NULL);
          yices_push(yp->ctx_);
        }
        ap->response_ = SMTLIB2_RESPONSE_SUCCESS;
    }
}

static void smtlib2_yices_parser_pop(smtlib2_parser_interface *p, int n)
{
    smtlib2_yices_parser *yp = (smtlib2_yices_parser *)p;
    smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *)p;

    if (ap->response_ != SMTLIB2_RESPONSE_ERROR) {
        smtlib2_term_parser *tp = ap->termparser_;
        while (n-- > 0) {
            char *def = (char *)smtlib2_vector_last(yp->defines_);
            smtlib2_yices_parametric_sort *ps = NULL;
            
            while (def != NULL) {
                smtlib2_term_parser_undefine_binding(tp, def);
                smtlib2_vector_pop(yp->defines_);
                def = (char *)smtlib2_vector_last(yp->defines_);
            }
            smtlib2_vector_pop(yp->defines_);
            
            ps = (smtlib2_yices_parametric_sort *)smtlib2_vector_last(
                yp->defines_sorts_);
            while (ps != NULL) {
                smtlib2_hashtable_erase(yp->sorts_, (intptr_t)ps);
                smtlib2_vector_pop(yp->defines_sorts_);
                smtlib2_yices_parametric_sort_delete(ps);
                ps = (smtlib2_yices_parametric_sort *)smtlib2_vector_last(
                    yp->defines_sorts_);
            }
            smtlib2_vector_pop(yp->defines_sorts_);

            def = (char *)smtlib2_vector_last(yp->names_);
            while (def != NULL) {
                intptr_t t = smtlib2_hashtable_get(yp->named_terms_,
                                                   (intptr_t)def);
                smtlib2_hashtable_erase(yp->named_terms_, (intptr_t)def);
                if (t) {
                    smtlib2_hashtable_erase(yp->term_names_, t);
                }
                
                smtlib2_vector_pop(yp->names_);
                free(def);
                def = (char *)smtlib2_vector_last(yp->names_);
            }
            smtlib2_vector_pop(yp->names_);
            
            yices_pop(yp->ctx_);
        }
        ap->response_ = SMTLIB2_RESPONSE_SUCCESS;
    }
}

static void smtlib2_yices_parser_assert_formula(smtlib2_parser_interface *p,
                                                smtlib2_term term)
{
    smtlib2_yices_parser *yp = (smtlib2_yices_parser *)p;
    smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *)p;

    int status;
    if (ap->response_ != SMTLIB2_RESPONSE_ERROR) {
      status = yices_assert_formula(yp->ctx_, (term_t)(intptr_t)term);
      
      if(status == 0) {
        ap->response_ = SMTLIB2_RESPONSE_SUCCESS;
      } else {
        ap->response_ = SMTLIB2_RESPONSE_ERROR;
      }
    }
}

static void smtlib2_yices_parser_check_sat(smtlib2_parser_interface *p)
{
    smtlib2_yices_parser *yp = (smtlib2_yices_parser *)p;
    smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *)p;
    
    if (ap->response_ != SMTLIB2_RESPONSE_ERROR) {
      smt_status_t s = yices_check_context(yp->ctx_, NULL);
      ap->response_ = SMTLIB2_RESPONSE_STATUS;
      switch (s) {
      case STATUS_UNSAT: ap->status_ = SMTLIB2_STATUS_UNSAT; break;
      case STATUS_SAT: ap->status_ = SMTLIB2_STATUS_SAT; break;
      default: ap->status_ = SMTLIB2_STATUS_UNKNOWN;
      }
    }
}


static void smtlib2_yices_parser_annotate_term(smtlib2_parser_interface *p,
                                               smtlib2_term term,
                                               smtlib2_vector *annotations)
{
  smtlib2_yices_parser *yp = (smtlib2_yices_parser *)p;
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *)p;

  if (ap->response_ != SMTLIB2_RESPONSE_ERROR) {
        size_t i;
        for (i = 0; i < smtlib2_vector_size(annotations); ++i) {
            const char **an = (const char **)smtlib2_vector_at(annotations, i);
            if (strcmp(an[0], ":named") == 0) {
                smtlib2_term t =
                    (smtlib2_term)smtlib2_hashtable_get(yp->named_terms_,
                                                        (intptr_t)an[1]);
                if (t != NULL && t != term) {
                    ap->response_ = SMTLIB2_RESPONSE_ERROR;
                    ap->errmsg_ = smtlib2_sprintf("annotation :named `%s' is "
                                                  "already in use", ap[1]);
                } else {
                    char *n = smtlib2_strdup(an[1]);
                    smtlib2_vector_push(yp->names_, (intptr_t)n);
                    smtlib2_hashtable_set(yp->named_terms_, (intptr_t)n,
                                          (intptr_t)term);
                    smtlib2_hashtable_set(yp->term_names_, (intptr_t)term,
                                          (intptr_t)n);
                }
            }
        }
    }
}


static void smtlib2_yices_parser_set_int_option(smtlib2_parser_interface *p,
                                                const char *keyword,
                                                int value)
{
    smtlib2_yices_parser *yp = (smtlib2_yices_parser *)p;
    smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *)p;

    if (ap->response_ != SMTLIB2_RESPONSE_ERROR) {
        if (strcmp(keyword, ":produce-unsat-cores") == 0) {
            yp->produce_unsat_cores_ = value;
        } else if (strcmp(keyword, ":produce-assignments") == 0) {
            yp->produce_assignments_ = value;
        } else if (strcmp(keyword, ":produce-models") == 0) {
            yp->produce_models_ = value;
        } else {
            smtlib2_abstract_parser_set_int_option(p, keyword, value);
        }
    }
}


static void smtlib2_yices_parser_get_assignment(smtlib2_parser_interface *p)
{
    smtlib2_yices_parser *yp = (smtlib2_yices_parser *)p;
    smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *)p;

    if (ap->response_ != SMTLIB2_RESPONSE_ERROR) {
      if (yp->produce_assignments_) {
            size_t i;
            model_t *m;
            
            m = yices_get_model(yp->ctx_, KEEP_SUBS);
            
            if (!m) {
                ap->response_ = SMTLIB2_RESPONSE_ERROR;
                ap->errmsg_ = smtlib2_strdup("error computing assignment");
                return;
            }

            ap->response_ = SMTLIB2_RESPONSE_MODEL;

            for (i = 0; i < smtlib2_vector_size(yp->names_); ++i) {
                intptr_t n = smtlib2_vector_at(yp->names_, i);
                if (n) {
                    intptr_t t;
                    if (smtlib2_hashtable_find(yp->named_terms_, n, &t)) {
                      
                      assert(yices_term_is_bool((term_t)t));
                      
                      int32_t v = -1;
                      
                      int status = yices_get_bool_value(m, (term_t)t, &v);
                      
                      assert(status == 0);

                      char *vv = NULL;
                      if (v == 1) {
                        vv = smtlib2_strdup("true");
                      } else if (v == 0) {
                        vv = smtlib2_strdup("false");
                      }
                      
                      if (vv) {
                        char *nn = smtlib2_strdup((char *)n);
                        smtlib2_vector_push(ap->response_data_,
                                            (intptr_t)nn);
                        smtlib2_vector_push(ap->response_data_,
                                            (intptr_t)vv);
                      }
                    } else {
                        ap->response_ = SMTLIB2_RESPONSE_ERROR;
                        ap->errmsg_ =
                            smtlib2_strdup("error computing assignment");
                        return;
                    }
                }
            }
      } else {
            ap->response_ = SMTLIB2_RESPONSE_ERROR;
            ap->errmsg_ = smtlib2_strdup(":produce-assignments option not set");
      }
    }
}

static void smtlib2_yices_parser_get_value(smtlib2_parser_interface *p,
                                           smtlib2_vector *terms)
{
    smtlib2_yices_parser *yp = (smtlib2_yices_parser *)p;
    smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *)p;

    if (ap->response_ != SMTLIB2_RESPONSE_ERROR) {
      if (yp->produce_models_) {
        size_t i;
        model_t *m;
        smtlib2_charbuf *buf;
        mpq_t ratval;
        
        m = yices_get_model(yp->ctx_, KEEP_SUBS);
        
        if (!m) {
          ap->response_ = SMTLIB2_RESPONSE_ERROR;
          ap->errmsg_ = smtlib2_strdup("error computing model");
          return;
        }
        
        buf = smtlib2_charbuf_new();
        smtlib2_charbuf_push_str(buf, "(.internal-parse-terms (");
        for (i = 0; i < smtlib2_vector_size(terms); ++i) {
          char *t = (char *)smtlib2_vector_at(terms, i);
          smtlib2_charbuf_push_str(buf, t);
          smtlib2_charbuf_push(buf, ' ');
        }
        smtlib2_charbuf_push_str(buf, "))");
            {
                smtlib2_scanner *scanner;
                smtlib2_sstream *stream;

                ap->internal_parsed_terms_enabled_ = true;
                
                stream = smtlib2_sstream_new(buf);
                scanner = smtlib2_scanner_new((smtlib2_stream *)stream);
                
                smtlib2_parse(scanner, p);

                smtlib2_scanner_delete(scanner);
                smtlib2_sstream_delete(stream);
                
                ap->internal_parsed_terms_enabled_ = false;
            }
            if (ap->response_ == SMTLIB2_RESPONSE_ERROR) {
                return;
            }
            
            ap->response_ = SMTLIB2_RESPONSE_MODEL;
            mpq_init(ratval);

            for (i = 0; i < smtlib2_vector_size(terms); ++i) {
              intptr_t n = smtlib2_vector_at(terms, i);
              intptr_t t = smtlib2_vector_at(ap->internal_parsed_terms_, i);

              char *vv = NULL;
              
              int32_t v = -1;

              type_t tp = yices_type_of_term((term_t)t);
              
              if(tp == yices_bool_type()) {
                yices_get_bool_value(m, (term_t)t, &v);
                if ( v == 1) {
                  vv = smtlib2_strdup("true");
                } else if (v == 0) {
                  vv = smtlib2_strdup("false");
                }
              } else if (tp == yices_real_type() || tp == yices_int_type()) {
                yices_get_mpq_value(m, (term_t)t, ratval);
                char *rn = mpz_get_str(NULL, 10, mpq_numref(ratval));
                if (mpz_cmp_ui(mpq_denref(ratval), 1) == 0) {
                  if (mpq_sgn(ratval) < 0) {
                    vv = smtlib2_sprintf("(- %s)", rn+1);
                  } else {
                    vv = smtlib2_strdup(rn);
                  }
                } else {
                  char *rd = mpz_get_str(NULL, 10,
                                         mpq_denref(ratval));
                  if (mpq_sgn(ratval) < 0) {
                    vv = smtlib2_sprintf("(/ (- %s) %s)", rn+1, rd);
                  } else {
                    vv = smtlib2_sprintf("(/ %s %s)", rn, rd);
                  }
                  free(rd);
                }
                free(rn);
              } else if (tp == yices_int_type()) {
                
              }
              /*
              yices_get_bool_value(m, (term_t)t, &v);
              
              if (v == 1) {
                vv = smtlib2_strdup("true");
              } else if (v == 0) {
                vv = smtlib2_strdup("false");
              }
              */
              /*
              if (!vv) {
                // Get the model value for this variable
                if (!yices_get_mpq_value(m, (term_t)t, ratval)) {
                  int v = -1;
                  int32_t status = yices_get_bool_value(m, (term_t)t, &v);
                  
                  assert(status == 0);

                  if (v == 1) {
                    vv = smtlib2_strdup("true");
                  } else if (v == 0) {
                    vv = smtlib2_strdup("false");
                  }
                } else {
                 
                }
              }
              */
              if (vv) {
                char *nn = smtlib2_strdup((char *)n);
                smtlib2_vector_push(ap->response_data_, (intptr_t)nn);
                smtlib2_vector_push(ap->response_data_, (intptr_t)vv);
              } else {
                ap->response_ = SMTLIB2_RESPONSE_ERROR;
                ap->errmsg_ =
                  smtlib2_strdup("error computing model");
                break;
              }
            }
            mpq_clear(ratval);
      } else {
        ap->response_ = SMTLIB2_RESPONSE_ERROR;
        ap->errmsg_ = smtlib2_strdup(":produce-models option not set");
      }
    }
}

static void smtlib2_yices_parser_get_unsat_core(smtlib2_parser_interface *p)
{
  smtlib2_abstract_parser *ap = (smtlib2_abstract_parser *)p;

  ap->response_ = SMTLIB2_RESPONSE_ERROR;
  ap->errmsg_ = smtlib2_strdup(":produce-unsat-cores not supported in Yices 2");
}

static smtlib2_term smtlib2_yices_parser_mk_function(smtlib2_context ctx,
                                                     const char *symbol,
                                                     smtlib2_sort sort,
                                                     smtlib2_vector *index,
                                                     smtlib2_vector *args)
{
  if (index) {
    return NULL;
  }
  if (args) {
    term_t f = yices_get_term_by_name(symbol);
    assert(f >= 0);
    if (f) {
      term_t *yices_args = malloc(sizeof(term_t)*smtlib2_vector_size(args));
      for(int i = 0; i < smtlib2_vector_size(args); i++) {
        yices_args[i] = (term_t)smtlib2_vector_at(args, i);
      }
      return (smtlib2_term)(intptr_t)yices_application(f, smtlib2_vector_size(args), yices_args);
    } else {
      return NULL;
    }
  } else {
    if (strcmp(symbol, "true") == 0) {
      return (smtlib2_term)(intptr_t)yices_true();
    } else if (strcmp(symbol, "false") == 0) {
      return (smtlib2_term)(intptr_t)yices_false();
    } else {
      term_t extra = yices_get_term_by_name(symbol);
      if(extra >= 0) {
        return (smtlib2_term)(intptr_t)extra;
      } else {
        /* TODO: typecheck */
        return NULL;
      }
    }
  }
}

static smtlib2_term smtlib2_yices_parser_mk_number(smtlib2_context ctx,
                                                   const char *rep,
                                                   unsigned int width,
                                                   unsigned int base)
{
    smtlib2_term ret;
    intptr_t v;
    if (width != 0) {
        mpz_t tmp;
        int i;
        int *bits = malloc(sizeof(int) * width);
        term_t ret;
        mpz_init(tmp);
        mpz_set_str(tmp, rep, base);
        for (i = 0; i < width; ++i) {
          bits[i] = mpz_tstbit(tmp, i);
        }
        mpz_clear(tmp);
        ret = yices_bvconst_from_array(width, bits);
        free(bits);
        return (smtlib2_term)(intptr_t)ret;
    } else if (base != 10) {
        return NULL;
    }
    ret = (smtlib2_term)(intptr_t)yices_parse_term(rep);
    if (!smtlib2_hashtable_find(((smtlib2_yices_parser *)ctx)->numbers_,
                                (intptr_t)ret, &v)) {
      smtlib2_hashtable_set(((smtlib2_yices_parser *)ctx)->numbers_,
                            (intptr_t)ret, (intptr_t)smtlib2_strdup(rep));
    }
    return ret;
}

SMTLIB2_YICES_DECLHANDLER(and)
{
  term_t *terms = malloc(sizeof(term_t) * smtlib2_vector_size(args));
  
  for(int i = 0; i < smtlib2_vector_size(args); i++) {
    terms[i] = smtlib2_vector_at(args, i);
  }
  term_t conj = yices_and(smtlib2_vector_size(args), terms);
  assert(conj >= 0);
  
  free(terms);

  return (smtlib2_term)(intptr_t)conj;
}

SMTLIB2_YICES_DECLHANDLER(or)
{
  term_t *terms = malloc(sizeof(term_t) * smtlib2_vector_size(args));
  
  for(int i = 0; i < smtlib2_vector_size(args); i++) {
    terms[i] = smtlib2_vector_at(args, i);
  }
  term_t disj = yices_or(smtlib2_vector_size(args), terms);
  assert(disj >= 0);
  
  free(terms);

  return (smtlib2_term)(intptr_t)disj;
}

SMTLIB2_YICES_DECLHANDLER(not)
{
  return (smtlib2_term)(intptr_t)yices_not((term_t)smtlib2_vector_at(args,0));
}

SMTLIB2_YICES_DECLHANDLER(implies)
{
  term_t ret = (term_t)(intptr_t)smtlib2_vector_last(args);
  int i;
  
  for (i = smtlib2_vector_size(args)-2; i >= 0; --i) {
    term_t a = (term_t)(intptr_t)smtlib2_vector_at(args, i);
    ret = yices_implies(a, ret);
  }
  return (smtlib2_term)(intptr_t)ret;
}

SMTLIB2_YICES_DECLHANDLER(eq)
{
  term_t ret = yices_eq((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                            (term_t)(intptr_t)smtlib2_vector_at(args, 1));
  size_t i;
  
  for (i = 2; i < smtlib2_vector_size(args); ++i) {
    term_t prev = (term_t)(intptr_t)smtlib2_vector_at(args, i-1);
    term_t cur = (term_t)(intptr_t)smtlib2_vector_at(args, i);
    ret = yices_eq(ret, yices_eq(prev, cur));
  }
  return (smtlib2_term)(intptr_t)ret;
}


SMTLIB2_YICES_DECLHANDLER(plus)
{
  term_t ret = yices_add((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                            (term_t)(intptr_t)smtlib2_vector_at(args, 1));
  size_t i;
  
  for (i = 2; i < smtlib2_vector_size(args); ++i) {
    term_t prev = (term_t)(intptr_t)smtlib2_vector_at(args, i-1);
    term_t cur = (term_t)(intptr_t)smtlib2_vector_at(args, i);
    ret = yices_add(ret, yices_add(prev, cur));
  }
  return (smtlib2_term)(intptr_t)ret;  
}

SMTLIB2_YICES_DECLHANDLER(times)
{
  term_t ret = yices_mul((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                         (term_t)(intptr_t)smtlib2_vector_at(args, 1));
  size_t i;
  
  for (i = 2; i < smtlib2_vector_size(args); ++i) {
    term_t prev = (term_t)(intptr_t)smtlib2_vector_at(args, i-1);
    term_t cur = (term_t)(intptr_t)smtlib2_vector_at(args, i);
    ret = yices_mul(ret, yices_mul(prev, cur));
  }
  return (smtlib2_term)(intptr_t)ret;
}

SMTLIB2_YICES_DECLHANDLER(minus)
{
  if (smtlib2_vector_size(args) == 1) {
    return (smtlib2_term)(intptr_t) yices_mul(yices_int32(-1), (term_t)(intptr_t)smtlib2_vector_at(args, 0));
  }
  
  term_t ret = yices_sub((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                         (term_t)(intptr_t)smtlib2_vector_at(args, 1));
  size_t i;
  
  for (i = 2; i < smtlib2_vector_size(args); ++i) {
    term_t prev = (term_t)(intptr_t)smtlib2_vector_at(args, i-1);
    term_t cur = (term_t)(intptr_t)smtlib2_vector_at(args, i);
    ret = yices_sub(ret, yices_sub(prev, cur));
  }
  return (smtlib2_term)(intptr_t)ret;
}

SMTLIB2_YICES_DECLHANDLER(leq)
{
  return (smtlib2_term)(intptr_t)yices_arith_leq_atom((term_t)(intptr_t)smtlib2_vector_at(args, 0), (term_t)(intptr_t)smtlib2_vector_at(args, 1));
}

SMTLIB2_YICES_DECLHANDLER(lt)
{
  return (smtlib2_term)(intptr_t)yices_arith_lt_atom((term_t)(intptr_t)smtlib2_vector_at(args, 0), (term_t)(intptr_t)smtlib2_vector_at(args, 1));
}

SMTLIB2_YICES_DECLHANDLER(geq)
{
  return (smtlib2_term)(intptr_t)yices_arith_lt_atom((term_t)(intptr_t)smtlib2_vector_at(args, 0), (term_t)(intptr_t)smtlib2_vector_at(args, 1));
}


SMTLIB2_YICES_DECLHANDLER(gt)
{
  return (smtlib2_term)(intptr_t)yices_arith_gt_atom((term_t)(intptr_t)smtlib2_vector_at(args, 0), (term_t)(intptr_t)smtlib2_vector_at(args, 1));
}

SMTLIB2_YICES_DECLHANDLER(ite)
{
  return (smtlib2_term)(intptr_t)yices_ite((term_t)(intptr_t)smtlib2_vector_at(args, 0), 
                                           (term_t)(intptr_t)smtlib2_vector_at(args, 1),
                                           (term_t)(intptr_t)smtlib2_vector_at(args, 2)
                                           );
}

SMTLIB2_YICES_DECLHANDLER(divide)
{
    smtlib2_yices_parser *p = (smtlib2_yices_parser *)ctx;
    intptr_t v, v2;
    if (smtlib2_hashtable_find(p->numbers_, smtlib2_vector_at(args, 1), &v)) {
      term_t e;
      char *n;
      if (smtlib2_hashtable_find(p->numbers_,
                                 smtlib2_vector_at(args, 0), &v2)) {
        n = smtlib2_sprintf("%s/%s", (const char *)v2, (const char *)v);
        e = yices_parse_term((const char *)n);
        free(n);
        return (smtlib2_term)(intptr_t)e;
      } else {
        n = smtlib2_sprintf("1/%s", (const char *)v);
      }
      e = yices_parse_term(n);
      free(n);
      if (e >= 0) {
        return (smtlib2_term)(intptr_t)yices_mul(e, (term_t)(intptr_t)smtlib2_vector_at(args, 0));
      } else {
            return NULL;
      }
    } else {
      return NULL;
    }
}

SMTLIB2_YICES_DECLHANDLER(distinct)
{
  term_t ret;
  size_t i;

  term_t* tmp = malloc(smtlib2_vector_size(args)*sizeof(term_t));
  
  assert(tmp);

  for(i = 0; i < smtlib2_vector_size(args); i++) {
    tmp[i] = (term_t)(intptr_t)smtlib2_vector_at(args, i);
  }

  ret = yices_distinct(smtlib2_vector_size(args), tmp);

  free(tmp);
  return (smtlib2_term)(intptr_t)ret;
}

SMTLIB2_YICES_DECLHANDLER(xor)
{
  term_t ret;
  size_t i;

  term_t* tmp = malloc(smtlib2_vector_size(args)*sizeof(term_t));
  
  assert(tmp);

  for(i = 0; i < smtlib2_vector_size(args); i++) {
    tmp[i] = (term_t)(intptr_t)smtlib2_vector_at(args, i);
  }

  ret = yices_xor(smtlib2_vector_size(args), tmp);

  free(tmp);
  return (smtlib2_term)(intptr_t)ret;
}

SMTLIB2_YICES_DECLHANDLER(nand)
{
  term_t ret;
  size_t i;

  term_t* tmp = malloc(smtlib2_vector_size(args)*sizeof(term_t));
  
  assert(tmp);

  for(i = 0; i < smtlib2_vector_size(args); i++) {
    tmp[i] = (term_t)(intptr_t)smtlib2_vector_at(args, i);
  }

  ret = yices_not(yices_and(smtlib2_vector_size(args), tmp));

  free(tmp);
  return (smtlib2_term)(intptr_t)ret;
}


SMTLIB2_YICES_DECLHANDLER(to_real)
{
  return (smtlib2_term)(intptr_t)smtlib2_vector_at(args, 0);
}

SMTLIB2_YICES_DECLHANDLER(concat)
{
  
  return (smtlib2_term)(intptr_t)yices_bvconcat((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                        (term_t)(intptr_t)smtlib2_vector_at(args, 1));
}

SMTLIB2_YICES_DECLHANDLER(bvnot)
{
  return (smtlib2_term)(intptr_t)yices_bvnot((term_t)(intptr_t)smtlib2_vector_at(args, 0));
}

SMTLIB2_YICES_DECLHANDLER(bvand)
{
    return (smtlib2_term)(intptr_t)yices_bvand((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                           (term_t)(intptr_t)smtlib2_vector_at(args, 1));    
}

SMTLIB2_YICES_DECLHANDLER(bvnand)
{
    return (smtlib2_term)(intptr_t)yices_bvnot(
                                            yices_bvand((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                                            (term_t)(intptr_t)smtlib2_vector_at(args, 1)));
}


SMTLIB2_YICES_DECLHANDLER(bvor)
{
    return (smtlib2_term)(intptr_t)yices_bvor((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                          (term_t)(intptr_t)smtlib2_vector_at(args, 1));    
}


SMTLIB2_YICES_DECLHANDLER(bvnor)
{
    return (smtlib2_term)(intptr_t)yices_bvnot(yices_bvor((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                       (term_t)(intptr_t)smtlib2_vector_at(args, 1)));
}


SMTLIB2_YICES_DECLHANDLER(bvxor)
{
    return (smtlib2_term)(intptr_t)yices_bvxor((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                           (term_t)(intptr_t)smtlib2_vector_at(args, 1));    
}


SMTLIB2_YICES_DECLHANDLER(bvxnor)
{
    return (smtlib2_term)(intptr_t)yices_bvnot(yices_bvxor((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                        (term_t)(intptr_t)smtlib2_vector_at(args, 1)));
}


SMTLIB2_YICES_DECLHANDLER(bvult)
{
    return (smtlib2_term)(intptr_t)yices_bvlt_atom((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                          (term_t)(intptr_t)smtlib2_vector_at(args, 1));    
}


SMTLIB2_YICES_DECLHANDLER(bvslt)
{
    return (smtlib2_term)(intptr_t)yices_bvslt_atom((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                           (term_t)(intptr_t)smtlib2_vector_at(args, 1));    
}


SMTLIB2_YICES_DECLHANDLER(bvule)
{
    return (smtlib2_term)(intptr_t)yices_bvle_atom((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                          (term_t)(intptr_t)smtlib2_vector_at(args, 1));    
}


SMTLIB2_YICES_DECLHANDLER(bvsle)
{
    return (smtlib2_term)(intptr_t)yices_bvsle_atom((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                           (term_t)(intptr_t)smtlib2_vector_at(args, 1));    
}


SMTLIB2_YICES_DECLHANDLER(bvugt)
{
    return (smtlib2_term)(intptr_t)yices_bvgt_atom((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                          (term_t)(intptr_t)smtlib2_vector_at(args, 1));    
}


SMTLIB2_YICES_DECLHANDLER(bvsgt)
{
    return (smtlib2_term)(intptr_t)yices_bvsgt_atom((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                           (term_t)(intptr_t)smtlib2_vector_at(args, 1));    
}


SMTLIB2_YICES_DECLHANDLER(bvuge)
{
    return (smtlib2_term)(intptr_t)yices_bvge_atom((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                          (term_t)(intptr_t)smtlib2_vector_at(args, 1));    
}


SMTLIB2_YICES_DECLHANDLER(bvsge)
{
    return (smtlib2_term)(intptr_t)yices_bvsge_atom((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                           (term_t)(intptr_t)smtlib2_vector_at(args, 1));    
}


SMTLIB2_YICES_DECLHANDLER(bvcomp)
{
  return (smtlib2_term)(intptr_t)yices_ite(
        yices_eq((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                 (term_t)(intptr_t)smtlib2_vector_at(args, 1)),yices_bvconst_uint64(1, 1),yices_bvconst_uint64(1, 0));
}

SMTLIB2_YICES_DECLHANDLER(bvneg)
{
  return (smtlib2_term)(intptr_t)yices_bvneg((term_t)(intptr_t)smtlib2_vector_at(args, 0));
}


SMTLIB2_YICES_DECLHANDLER(bvadd)
{
    return (smtlib2_term)(intptr_t)yices_bvadd((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                           (term_t)(intptr_t)smtlib2_vector_at(args, 1));    
}


SMTLIB2_YICES_DECLHANDLER(bvsub)
{
    return (smtlib2_term)(intptr_t)yices_bvsub((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                           (term_t)(intptr_t)smtlib2_vector_at(args, 1));    
}


SMTLIB2_YICES_DECLHANDLER(bvmul)
{
    return (smtlib2_term)(intptr_t)yices_bvmul((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                           (term_t)(intptr_t)smtlib2_vector_at(args, 1));    
}


SMTLIB2_YICES_DECLHANDLER(bvudiv) { 

  return NULL; /* TODO */ 
}

SMTLIB2_YICES_DECLHANDLER(bvsdiv) { 
  return NULL; /* TODO */ 
}

SMTLIB2_YICES_DECLHANDLER(bvsmod) { 
  return NULL; /* TODO */ 
}

SMTLIB2_YICES_DECLHANDLER(bvurem) { 
  return NULL; /* TODO */ 
}

SMTLIB2_YICES_DECLHANDLER(bvsrem) { 
  return NULL; /* TODO */ 
}

SMTLIB2_YICES_DECLHANDLER(bvshl)  { 
  return NULL; /* TODO */ 
}

SMTLIB2_YICES_DECLHANDLER(bvlshr) { 
  return NULL; /* TODO */ 
}

SMTLIB2_YICES_DECLHANDLER(bvashr) { 
  return NULL; /* TODO */ 
}

SMTLIB2_YICES_DECLHANDLER(extract)
{
  size_t msb = (size_t)smtlib2_vector_at(idx, 0);
  size_t lsb = (size_t)smtlib2_vector_at(idx, 1);
  return (smtlib2_term)(intptr_t)yices_bvextract(lsb, msb , (term_t)(intptr_t)smtlib2_vector_at(args, 0));
}

SMTLIB2_YICES_DECLHANDLER(repeat)
{
  size_t amount = (size_t)smtlib2_vector_at(idx, 0);
  term_t t = (term_t)(intptr_t)smtlib2_vector_at(args, 0);
  term_t ret = t;
  size_t i;
  for (i = 1; i < amount; ++i) {
    ret = yices_bvconcat(ret, t);
  }
  return (smtlib2_term)(intptr_t)ret;
}

SMTLIB2_YICES_DECLHANDLER(zero_extend)
{
  size_t amount = (uint32_t)smtlib2_vector_at(idx, 0);
  return (smtlib2_term)(intptr_t)yices_zero_extend((term_t)(intptr_t)smtlib2_vector_at(args, 0), amount);
}

SMTLIB2_YICES_DECLHANDLER(sign_extend)
{
  size_t amount = (size_t)smtlib2_vector_at(idx, 0);
  return (smtlib2_term)(intptr_t)yices_zero_extend((term_t)(intptr_t)smtlib2_vector_at(args, 0),
                                                   amount);
}

SMTLIB2_YICES_DECLHANDLER(rotate_left) { return NULL; /* TODO */ }
SMTLIB2_YICES_DECLHANDLER(rotate_right)  { return NULL; /* TODO */ }


/*----------------------------------------------------------------------------*/

static smtlib2_yices_parametric_sort *smtlib2_yices_parametric_sort_new(
    const char *name, smtlib2_vector *params)
{
    smtlib2_yices_parametric_sort *ret =
        (smtlib2_yices_parametric_sort *)malloc(
            sizeof(smtlib2_yices_parametric_sort));
    ret->name_ = smtlib2_strdup(name);
    ret->params_ = NULL;
    if (params) {
        ret->params_ = smtlib2_vector_new();
        smtlib2_vector_copy(params, ret->params_);
    }
    return ret;
}


static void smtlib2_yices_parametric_sort_delete(
    smtlib2_yices_parametric_sort *s)
{
    if (s->params_) {
      smtlib2_vector_delete(s->params_);
    }
    free(s->name_);
    free(s);
}

static uint32_t smtlib2_yices_parametric_sort_hashfun(intptr_t s)
{
  smtlib2_yices_parametric_sort *ps = (smtlib2_yices_parametric_sort *)s;
    uint32_t ret;
    ret = smtlib2_hashfun_str((intptr_t)ps->name_);
    if (ps->params_) {
        size_t i;
        for (i = 0; i < smtlib2_vector_size(ps->params_); ++i) {
            ret = 5 * ret + (uint32_t)smtlib2_vector_at(ps->params_, i);
        }
    }
    return ret;
}

static bool smtlib2_yices_parametric_sort_eqfun(intptr_t s1, intptr_t s2)
{
    smtlib2_yices_parametric_sort *ps1 = (smtlib2_yices_parametric_sort *)s1;
    smtlib2_yices_parametric_sort *ps2 = (smtlib2_yices_parametric_sort *)s2;

    if (ps1 == ps2) {
        return true;
    }
    if ((ps1->params_ == NULL) != (ps2->params_ == NULL)) {
        return false;
    }
    if (strcmp(ps1->name_, ps2->name_) != 0) {
        return false;
    }
    if (ps1->params_) {
        size_t i;
        if (smtlib2_vector_size(ps1->params_) !=
            smtlib2_vector_size(ps2->params_)) {
            return false;
        }
        for (i = 0; i < smtlib2_vector_size(ps1->params_); ++i) {
            if (smtlib2_vector_at(ps1->params_, i) !=
                smtlib2_vector_at(ps2->params_, i)) {
                return false;
            }
        }
    }
    return true;
}
