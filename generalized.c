/***** ltl3dra : generalized.c *****/

/* Written by Denis Oddoux, LIAFA, France                                 */
/* Copyright (c) 2001  Denis Oddoux                                       */
/* Modified by Paul Gastin, LSV, France                                   */
/* Copyright (c) 2007  Paul Gastin                                        */
/* Modified by Tomas Babiak, FI MU, Brno, Czech Republic                  */
/* Copyright (c) 2012  Tomas Babiak                                       */
/* Modified by Tomas Babiak and Frantisek Blahoudek, Brno, Czech Republic */
/* Copyright (c) 2013  Tomas Babiak and Frantisek Blahoudek               */
/*                                                                        */
/* This program is free software; you can redistribute it and/or modify   */
/* it under the terms of the GNU General Public License as published by   */
/* the Free Software Foundation; either version 2 of the License, or      */
/* (at your option) any later version.                                    */
/*                                                                        */
/* This program is distributed in the hope that it will be useful,        */
/* but WITHOUT ANY WARRANTY; without even the implied warranty of         */
/* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          */
/* GNU General Public License for more details.                           */
/*                                                                        */
/* You should have received a copy of the GNU General Public License      */
/* along with this program; if not, write to the Free Software            */
/* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA*/
/*                                                                        */
/* Based on the translation algorithm by Gastin and Oddoux,               */
/* presented at the 13th International Conference on Computer Aided       */
/* Verification, CAV 2001, Paris, France.                                 */
/* Proceedings - LNCS 2102, pp. 53-65                                     */
/*                                                                        */
/* and on paper by                                                        */
/* T. Babiak, M. Kretinsky, V. Rehak, and J. Strejcek,                    */
/* LTL to Buchi Automata Translation: Fast and More Deterministic         */
/* presented at the 18th International Conference on Tools and            */
/* Algorithms for the Construction and Analysis of Systems (TACAS 2012)   */
/*                                                                        */
/* The translation to deterministic Rabin automata is based on paper by   */
/* T. Babiak, F. Blahoudek, M. Kretinsky, and J. Strejcek                 */
/* Effective Translation of LTL to Deterministic Rabin Automata:          */
/* Beyond the (F,G)-Fragment (2013)                                       */
/* In 11th International Symposium on Automated Technology for            */
/* Verification and Analysis (ATVA 2013)                                  */

#include "ltl3dra.h"
#include <bdd.h>
#include <map>
#include <set>
#include <algorithm>
#define NO 0
#define YES 1
/* Define whether to use supplementary outputs or not. */
#define SUPP_OUT NO

/* When defined, auxiliary dictionaries are used to speed up searching */
/* among existing states.             Comment to disable.              */
#define DICT

/********************************************************************\
|*              Structures and shared variables                     *|
\********************************************************************/

extern FILE *tl_out;
extern std::map<cset, ATrans*> **transition;

extern int tl_verbose, tl_stats, tl_simp_diff, tl_simp_fly, tl_fjtofj, tl_ltl3ba,
  tl_simp_scc, *final_set, node_id, tl_postpone, tl_f_components, tl_rem_scc, node_size,
  tl_det_m, print_or, tl_spot_out, tl_hoaf, predicates;
extern char **sym_table;
extern Node **label;

GState *gstack, *gremoved, *gstates, **init;
GScc *gscc_stack;
#ifdef DICT
std::map<cset, GState*> gsDict;
#endif
std::map<cset, ATrans*> *empty_t;
int init_size = 0, gstate_id = 1, gstate_count = 0, gtrans_count = 0, compute_directly;
int *final, scc_rank, scc_id, scc_size, *bad_scc, *non_term_scc;
cset *fin;

extern int *INFp_nodes, *UXp_nodes, *GFcomp_nodes, *Falpha_nodes, **predecessors, *tecky, *V_nodes,
           *is_Gs, *is_UG, *UG_succ, *UG_pred;

void print_generalized();
void remove_redundand_targets(cset *set, cset *fin);

int included_big_set(cset *set_1, cset *set_2, GState *s);

/********************************************************************\
|*        Implementation of some methods of auxiliary classes        *|
\********************************************************************/

bool GStateComp::operator() (const GState* l, const GState* r) const {
  return (*l->nodes_set < *r->nodes_set);
}

void AProd::merge_to_prod(AProd *p1, int i) {
  if(!p1->prod) {
    if(prod) {
      free_atrans(prod, 0);
      prod = (ATrans *)0;
      prod_to.clear();
    }
    return;
  }
  if(!prod)
    prod = emalloc_atrans();
  prod->label = p1->prod->label;
  copy_set(p1->prod->bad_nodes, prod->bad_nodes, 0);
  prod_to = p1->prod_to;
  prod_to.insert(i);
}

void AProd::merge_to_prod(AProd *p1, const std::pair<const cset, ATrans*> &trans) {
  if(!p1->prod || !trans.second) {
    if(prod) {
      free_atrans(prod, 0);
      prod = (ATrans *)0;
      prod_to.clear();
    }
    return;
  }
  if(!prod)
    prod = emalloc_atrans();

  prod->label = p1->prod->label & trans.second->label;
  if(prod->label == bdd_false()) {
    free_atrans(prod, 0);
    prod = (ATrans *)0;
  } else {
    do_merge_sets(prod->bad_nodes, p1->prod->bad_nodes, trans.second->bad_nodes, 0);
    prod_to.merge(p1->prod_to, trans.first);
  }
}

void cGTrans::decrement_incoming(void) {
  std::map<GState*, std::map<cset, bdd>, GStateComp>::iterator t;
  for(t = trans.begin(); t != trans.end(); t++)
    t->first->incoming = t->first->incoming - t->second.size();
}

/* Check wheter the newly build transitions dominates any existing or is dominated */
/* true is returned if the new transition shoul be added */
bool cGTrans::check_dominance(ATrans *t, cset *t_to, cset* fin, int acc, int &state_trans, GState* s) {
  std::map<GState*, std::map<cset, bdd>, GStateComp>::iterator t1, tx1;
  std::map<cset, bdd>::iterator t2, tx2;
  if (compute_directly || !tl_simp_fly) return 1;
  for(t1 = trans.begin(); t1 != trans.end(); ) {
    if(//!compute_directly && tl_simp_fly &&
       included_big_set(t_to, t1->first->nodes_set, s)) {
//       t_to->is_subset_of(*t1->first->nodes_set)) {
      for(t2 = t1->second.begin(); t2 != t1->second.end(); ) {
        if(((t->label << t2->second) == bdd_true()) &&
           ((!tl_ltl3ba && (*fin == t2->first)) ||
            (tl_ltl3ba && t2->first.is_subset_of(*fin)) ||
            (!acc && t2->first.is_subset_of(*fin)))) { /* old transition t2 is redundant - remove t2 */
          t1->first->incoming--;
          tx2 = t2++;
          t1->second.erase(tx2);
          state_trans--;
        } else {
          t2++;
        }
      }
      if (t1->second.empty()) {
        tx1 = t1++;
        trans.erase(tx1);
        continue;
      }
    }
    if(//!compute_directly && tl_simp_fly &&
       included_big_set(t1->first->nodes_set, t_to, s)) {
//       t1->first->nodes_set->is_subset_of(*t_to)) {
      for(t2 = t1->second.begin(); t2 != t1->second.end(); t2++) {
        if(((t2->second << t->label) == bdd_true()) &&
           ((!tl_ltl3ba && (t2->first == *fin)) ||
            (tl_ltl3ba && fin->is_subset_of(t2->first)) ||
            (!acc && t2->first.is_subset_of(*fin)))) { /* new transition t is redundant - do not add t */
          return 0;
        }
      }
    }
    t1++;
  }
  return 1;
}

bool cGTrans::determinize(ATrans *t, cset *t_to, cset* fin, int acc, int &state_trans, GState* s) {
  std::map<GState*, std::map<cset, bdd>, GStateComp>::iterator t1, tx1;
  std::map<cset, bdd>::iterator t2, tx2;
  for(t1 = trans.begin(); t1 != trans.end(); ) {
    if (t_to->is_subset_of(*t1->first->nodes_set)) {
      for(t2 = t1->second.begin(); t2 != t1->second.end(); ) {
        if (t2->first.is_subset_of(*fin) &&
            ((t2->first != *fin) || (*t1->first->nodes_set != *t_to))) {
          t2->second &= ! t->label;
          if (t2->second == bdd_false()) {
            tx2 = t2++;
            t1->second.erase(tx2);
          } else {
            t2++;
          }
        } else {
          t2++;
        }
      }
      if (t1->second.empty()) {
        tx1 = t1++;
        trans.erase(tx1);
        continue;
      }
    }
    if (t1->first->nodes_set->is_subset_of(*t_to)) {
      for(t2 = t1->second.begin(); t2 != t1->second.end(); t2++) {
        if (fin->is_subset_of(t2->first) &&
            ((t2->first != *fin) || (*t1->first->nodes_set != *t_to))) {
          t->label &= ! t2->second;
          if (t->label == bdd_false()) {
            return 0;
          }
        }
      }
    }
    t1++;
  }
  return 1;
}

bool cGTrans::add_trans(bdd label, cset *fin, GState* to) {
  bdd *l = &((trans[to])[*fin]);
  if (*l == bdd_false()) {
    *l = label;
    return 1;
  } else {
    *l |= label;
    return 0;
  }
}

/********************************************************************\
|*        Simplification of the generalized Buchi automaton         *|
\********************************************************************/

void free_gstate(GState *s) /* frees a state and its transitions */
{
  s->trans->decrement_incoming();
  // free trans
  delete s->trans;
  // free nodes_set
  delete s->nodes_set;
  tfree(s);
}

GState *remove_gstate(GState *s, GState *s1) /* removes a state */
{
  GState *prv = s->prv;
  s->prv->nxt = s->nxt;
  s->nxt->prv = s->prv;
  delete s->trans;
  s->trans = (cGTrans *)0;
//  delete s->nodes_set; // Do not delete so the order does not change.
//  s->nodes_set = 0;
  s->nxt = gremoved->nxt;
  gremoved->nxt = s;
  s->prv = s1;
  for(s1 = gremoved->nxt; s1 != gremoved; s1 = s1->nxt)
    if(s1->prv == s)
      s1->prv = s->prv;
  return prv;
} 

int simplify_gtrans() /* simplifies the transitions */
{
  int changed = 0;
  GState *s;
  std::map<GState*, std::map<cset, bdd>, GStateComp>::iterator t;
  std::map<cset, bdd>::iterator gt1, gt2, gx;
  std::map<cset, bdd>::reverse_iterator rt1, rt2, rx;

  for(s = gstates->nxt; s != gstates; s = s->nxt) {
    if (!tl_f_components || !included_set(s->nodes_set->get_set(), GFcomp_nodes, 0)) {
      t = s->trans->begin();
      while(t != s->trans->end()) { /* tries to remove trans in t */
        /* acceptance conditions may be ignored - try all combinations */
        if (tl_simp_scc && ((s->incoming != t->first->incoming) || in_set(bad_scc, s->incoming))) {
          for (gt1 = t->second.begin(); gt1 != t->second.end(); gt1++) {
            for (gt2 = t->second.begin(); gt2 != t->second.end(); ) {
              if ((gt1 != gt2) &&
                  (gt1->second << gt2->second) == bdd_true()) {
                //remove gt2;
                gx = gt2++;
                t->second.erase(gx);
                changed++;
              } else {
                gt2++;
              }
            }
          }
        } else {
          /* acceptance conditions matter - benefit from the ordering */
          for (rt1 = t->second.rbegin(); rt1 != t->second.rend(); rt1++) {
            for (rt2 = rt1, rt2++; rt2 != t->second.rend(); rt2++) {
              if (rt2->first.is_subset_of(rt1->first) && 
                  ((rt1->second << rt2->second) == bdd_true())) {
                // remove rt2
                rx = rt2--;
                t->second.erase(rx->first);
                changed++;
              }
            }
          }
        }
        t++;
      }
    }
  }
  return changed;
}

void retarget_all_gtrans()
{             /* redirects transitions before removing a state from the automaton */
  GState *s;
  std::map<GState*, std::map<cset, bdd>, GStateComp>::iterator t1, tx;
  std::map<cset, bdd>::iterator t2;
  int i;
  for (i = 0; i < init_size; i++)
    if (init[i] && !init[i]->trans) /* init[i] has been removed */
      init[i] = init[i]->prv;
  for (s = gstates->nxt; s != gstates; s = s->nxt)
    for (t1 = s->trans->begin(); t1 != s->trans->end(); )
      if (!t1->first->trans) { /* t->to has been removed */
        if(t1->first->prv) { /* t->to->prv have some transitions - retarget there */
          std::map<cset, bdd> *m = &((*s->trans)[t1->first->prv]);
          if (m->empty()) {
            *m = (*s->trans)[t1->first];
          } else {
            for (t2 = t1->second.begin(); t2 != t1->second.end(); t2++) {
              bdd *l = &((*m)[t2->first]);
              if (*l == bdd_false()) {
                *l = t2->second;
              } else {
                *l |= t2->second;
              }              
            }
          }
        }
        tx = t1++;
        s->trans->erase(tx);
      } else {
        t1++;
      }
  while(gremoved->nxt != gremoved) { /* clean the 'removed' list */
    s = gremoved->nxt;
    gremoved->nxt = gremoved->nxt->nxt;
    if(s->nodes_set) delete s->nodes_set;
    tfree(s);
  }
}

int all_gtrans_match(GState *a, GState *b, int use_scc) 
{ /* decides if the states are equivalent */
  if (a->trans == b->trans) return 1; // sentinel state found
  if (use_scc) {
    // First check whether both states have transitions to same states
    if (a->trans->size() != b->trans->size())
      return 0;

    std::map<GState*, std::map<cset, bdd>, GStateComp>::iterator a_t1, b_t1;
    std::map<cset, bdd>::iterator a_t2, b_t2;
    
    for (a_t1 = a->trans->begin(), b_t1 = b->trans->begin(); a_t1 != a->trans->end(); a_t1++, b_t1++) {
      // We must have tranisions going to the same state
      if (a_t1->first != b_t1->first)
        return 0;
        
      // Check whether both states have same transitions going to that same state
      // Firs we check whether acceptance conditions may be ignored
      if (in_set(bad_scc, a->incoming) ||
          in_set(bad_scc, b->incoming) ||
          (a->incoming != a_t1->first->incoming) ||
          (b->incoming != b_t1->first->incoming)) {
        // Yes, acceptance conditions do not matter
        // For each transition from a (a_t1) find a mattching transition from b (b_t1) with the same label
        for(a_t2 = a_t1->second.begin(); a_t2 != a_t1->second.end(); a_t2++) {
          for(b_t2 = b_t1->second.begin(); b_t2 != b_t1->second.end(); b_t2++) {
            if (a_t2->second == b_t2->second)
              break;
          }
          // If no transtion was found - return 0
          if (b_t2 == b_t1->second.end())
            return 0;
        }
        // Other direction: For each transition from b (b_t1) find a mattching transition from a (a_t1) with the same label
        for(b_t2 = b_t1->second.begin(); b_t2 != b_t1->second.end(); b_t2++) {
          for(a_t2 = a_t1->second.begin(); a_t2 != a_t1->second.end(); a_t2++) {
            if (a_t2->second == b_t2->second)
              break;
          }
          // If no transtion was found - return 0
          if (a_t2 == a_t1->second.end())
            return 0;
        }
      } else {
        // Acceptance conditions matter - all transitions must be exactly same
        if (a_t1->second != b_t1->second)
          return 0;
      }
    }
    return 1;
  } else {
    // Let std::map handle comparision
    if (*a->trans != *b->trans)
      return 0;
  }
  return 1;
}

int simplify_gstates() /* eliminates redundant states */
{
  int changed = 0;
  GState *a, *b;

  for(a = gstates->nxt; a != gstates; a = a->nxt) {
    if(a->trans->empty()) { /* a has no transitions */
      a = remove_gstate(a, (GState *)0);
      changed++;
      continue;
    }
    gstates->trans = a->trans;
    b = a->nxt;
    while(!all_gtrans_match(a, b, tl_simp_scc)) b = b->nxt;
    if(b != gstates) { /* a and b are equivalent */
      /* if scc(a)>scc(b) and scc(a) is non-trivial then all_gtrans_match(a,b,use_scc) must fail */
      if(a->incoming > b->incoming) /* scc(a) is trivial */
        a = remove_gstate(a, b);
      else /* either scc(a)=scc(b) or scc(b) is trivial */ 
        remove_gstate(b, a);
      changed++;
      continue;
    }
    if(tl_rem_scc && !in_set(non_term_scc, a->incoming) && in_set(bad_scc, a->incoming)) {
      a = remove_gstate(a, 0);
      changed++;
    }
  }
  retarget_all_gtrans();
  return changed;
}

int gdfs(GState *s) {
  std::map<GState*, std::map<cset, bdd>, GStateComp>::iterator t1;
  GScc *c;
  GScc *scc = (GScc *)tl_emalloc(sizeof(GScc));
  scc->gstate = s;
  scc->rank = scc_rank;
  scc->theta = scc_rank++;
  scc->nxt = gscc_stack;
  gscc_stack = scc;

  s->incoming = 1;

  if (tl_f_components && included_set(s->nodes_set->get_set(), GFcomp_nodes, 0)) { /* kyticka */
    scc->gstate->incoming = scc_id++;
    gscc_stack = scc->nxt;
    return scc->theta;
  }

  for (t1 = s->trans->begin(); t1 != s->trans->end(); t1++) {
    if (t1->first->incoming == 0) {
      int result = gdfs(t1->first);
      scc->theta = std::min(scc->theta, result);
    }
    else {
      for(c = gscc_stack->nxt; c != 0; c = c->nxt)
        if(c->gstate == t1->first) {
          scc->theta = std::min(scc->theta, c->rank);
          break;
        }
    }
  }
  if(scc->rank == scc->theta) {
    while(gscc_stack != scc) {
      gscc_stack->gstate->incoming = scc_id;
      gscc_stack = gscc_stack->nxt;
    }
    scc->gstate->incoming = scc_id++;
    gscc_stack = scc->nxt;
  }
  return scc->theta;
}

void simplify_gscc() {
  GState *s;
  std::map<GState*, std::map<cset, bdd>, GStateComp>::iterator t1;
  std::map<cset, bdd>::iterator t2;
  int i, **scc_final;
  scc_rank = 1;
  gscc_stack = 0;
  scc_id = 1;

  if(gstates == gstates->nxt) return;

  for(s = gstates->nxt; s != gstates; s = s->nxt)
    s->incoming = 0; /* state color = white */

  for(i = 0; i < init_size; i++)
    if(init[i] && init[i]->incoming == 0)
      gdfs(init[i]);

  scc_final = (int **)tl_emalloc(scc_id * sizeof(int *));
  for(i = 0; i < scc_id; i++)
    scc_final[i] = make_set(-1,0);

  scc_size = (scc_id + 1) / (8 * sizeof(int)) + 1;
  bad_scc=make_set(-1,2);
  non_term_scc = make_set(-1,2);

  for(s = gstates->nxt; s != gstates; s = s->nxt)
    if(s->incoming == 0)
      s = remove_gstate(s, 0);
    else
      for (t1 = s->trans->begin(); t1 != s->trans->end(); t1++)
        if(t1->first->incoming == s->incoming)
          for (t2 = t1->second.begin(); t2 != t1->second.end(); t2++)
            merge_sets(scc_final[s->incoming], t2->first.get_set(), 0);
        else
          add_set(non_term_scc, s->incoming);

  for(i = 0; i < scc_id; i++)
    if(!included_set(final_set, scc_final[i], 0))
       add_set(bad_scc, i);

  for(i = 0; i < scc_id; i++)
    tfree(scc_final[i]);
  tfree(scc_final);
}

/********************************************************************\
|*        Generation of the generalized Buchi automaton             *|
\********************************************************************/

int is_final(cset *from, ATrans *at, cset *at_to, int i) /*is the transition final for i ?*/
{
  std::map<cset, ATrans*>::iterator t;
  int in_to;
  if((tl_fjtofj && !at_to->is_elem(i)) ||
    (!tl_fjtofj && !from->is_elem(i))) return 1;
  in_to = at_to->is_elem(i);
  at_to->erase(i);
  for(t = transition[i]->begin(); t != transition[i]->end(); t++)
    if(t->first.is_subset_of(*at_to) &&
       ((t->second->label << at->label) == bdd_true())) {
      if(in_to) at_to->insert(i);
      return 1;
    }
  if(in_to) at_to->insert(i);
  return 0;
}

GState *find_gstate(cset *set, GState *s) 
{ /* finds the corresponding state, or creates it */

  if(tl_f_components && compute_directly) return s;

  if(*set == *s->nodes_set) return s; /* same state */

#ifdef DICT
  // find the state
/*  std::map<cset, GState*>::iterator gs_temp = gsDict.find(*set);
  if (gs_temp != gsDict.end())
    return gs_temp->second;*/
  GState** st_temp = &(gsDict[*set]);
  if (*st_temp != NULL) {
    return *st_temp;
  }
#else
  s = gstack->nxt; /* in the stack */
  gstack->nodes_set = set;
  while(*set != *s->nodes_set)
    s = s->nxt;
  if(s != gstack) return s;

  s = gstates->nxt; /* in the solved states */
  gstates->nodes_set = set;
  while(*set != *s->nodes_set)
    s = s->nxt;
  if(s != gstates) return s;

  s = gremoved->nxt; /* in the removed states */
  gremoved->nodes_set = set;
  while(*set != *s->nodes_set)
    s = s->nxt;
  if(s != gremoved) return s;
#endif

  s = (GState *)tl_emalloc(sizeof(GState)); /* creates a new state */
  s->id = (set->empty()) ? 0 : gstate_id++;
  s->incoming = 0;
  s->nodes_set = new cset(*set);
  s->trans = new cGTrans();
  s->nxt = gstack->nxt;
  gstack->nxt = s;
#ifdef DICT
  // Insert a new state into dictionary
//  gsDict.insert(std::pair<cset, GState*>(*s->nodes_set, s));
  *st_temp = s;
#endif
  return s;
}

int check_postpone(int *list) {
  int i, j, out = 0;
  
  if (list[0] <= 2) return 0;
  
  for(i = 1; i < list[0]; i++) {
    if (in_set(UXp_nodes, list[i]) && !in_set(tecky, list[i])) {
      if (!in_set(INFp_nodes, list[i])) {
        return 2;
      } else {
        out = 1;
      }
    }
  }
  return out;
}

/* Checks whether node is a cuccesor of some GF state in list */
int is_succ_off_some_GF(int *list, int node) {
  int j;
  for(j = 1; j < list[0]; j++) {
     if (in_set(GFcomp_nodes, list[j])) {
        if (in_set(predecessors[node], list[j])) return 1;
     }
  }
  return 0;
}

void remove_redundand_targets(cset *set, cset *fin) {
  int i, *list;
  list = set->to_list();

#if SUPP_OUT == YES
  fprintf(tl_out, "Remove: ");
/*  for(i = 1; i < list[0]; i++) {
      fprintf(tl_out, "%d, ", list[i]);
  }
  fprintf(tl_out, "\n");*/
#endif
 
  for(i = 1; i < list[0]; i++) {
    if (in_set(Falpha_nodes, list[i]) &&
        is_succ_off_some_GF(list, list[i])) {
#if SUPP_OUT == YES
      fprintf(tl_out, "%d, ", list[i]);
#endif
      set->erase(list[i]);
      fin->erase(list[i]);
    }
  }

#if SUPP_OUT == YES
  fprintf(tl_out, "\n");
#endif

  tfree(list);
}

int can_be_optimized(cset *set) {
  int i, *list;
  list = set->to_list();

  if (list[0] <= 2) return 0;

#if SUPP_OUT == YES
  fprintf(tl_out, "Can be optimized (1): ");
  for(i = 1; i < list[0]; i++) {
    fprintf(tl_out, "%d, ", list[i]);
  }
  fprintf(tl_out, "\n");
#endif

  for(i = 1; i < list[0]; i++) {
    if (!in_set(GFcomp_nodes, list[i]) && !in_set(Falpha_nodes, list[i])) {
/*        && !in_set(UXp_nodes, list[i])) { -- sposobovalo nekorektnost ale domysliet */
      tfree(list);
      return 0;
    }
  }

  tfree(list);
  return 1;
}

int check_if_acc_node(int *list) {
  int i;
  
  for(i = 1; i < list[0]; i++) {
    if (!in_set(V_nodes, list[i]) && !in_set(tecky, list[i]))
      return 0;
  }
  return 1;
}

int included_big_set(cset *set_1, cset *set_2, GState *s) {
/*  if (empty_intersect_sets(set_1, set_2, 0)) return 0;*/
  if (tl_ltl3ba && UG_pred != NULL && 
      (set_1 != set_2) && (set_1 != s->nodes_set) &&
      (set_1 != s->nodes_set) &&  !empty_intersect_sets(is_Gs, set_2->get_set(), 0)) {
    int *set = make_set(-1, 0);
    copy_set(set_2->get_set(), set, 0);
    int ii, jj, mod = 8 * sizeof(int);
            
    for(ii = 0; ii < node_size; ii++) {
      for(jj = 0; jj < 8 * sizeof(int); jj++) {
        if((set_2->get_set())[ii] & (1 << jj)) {
          if(UG_pred[(mod * ii + jj) - 1]) {
/*            printf("Pridavam: %d\n", UG_pred[(mod * ii + jj) - 1]);*/
            add_set(set, UG_pred[(mod * ii + jj) - 1]);
          }
        }
      }
    }
/*    printf("set_1: ");
    print_set(set_1, 0);
    printf("\nset: ");
    print_set(set, 0);
    printf("\n");*/
    int out = included_set(set_1->get_set(), set, 0);
    tfree(set);
    return out;
  }
  return included_set(set_1->get_set(), set_2->get_set(), 0);
}

void make_gtrans(GState *s) { /* creates all the transitions from a state */
  int i, *list, state_trans = 0, trans_exist = 1, postpone;
  GState *s1;
  ATrans *t1; /* *free, */
  cset *t1_to;
  AProd *prod = new AProd(); /* initialization */
  prod->nxt = prod;
  prod->prv = prod;
  list = s->nodes_set->to_list();

//  std::cout << std::endl << "Spracuvam stav: " << s->id << " s->nodes_set: " << *s->nodes_set << std::endl;

#if SUPP_OUT == YES  
    fprintf(tl_out, "Check: ");
    for(i = 1; i < list[0]; i++) {
            fprintf(tl_out, "%d, ", list[i]);
    }
    fprintf(tl_out, "\n");
#endif

  /* Check whether state is a GF component and can be computed directly */
  if (tl_f_components && included_set(s->nodes_set->get_set(), GFcomp_nodes, 0)) {
#if SUPP_OUT == YES  
    fprintf(tl_out, "Directly: ");
    for(i = 1; i < list[0]; i++) {
        fprintf(tl_out, "%d, ", list[i]);
    }
    fprintf(tl_out, "\n");
#endif
    compute_directly = 1;
    postpone=0;
  } else {
    compute_directly = 0;
    if (tl_postpone && !empty_intersect_sets(s->nodes_set->get_set(), INFp_nodes, 0))
      postpone = check_postpone(list);
    else
      postpone = 0; 
/*    fprintf(tl_out, "Not directly\n");*/
  }
  
#if SUPP_OUT == YES
  if (postpone) {  
    fprintf(tl_out, "Postpone (%d): ", postpone);
    for(i = 1; i < list[0]; i++) {
        fprintf(tl_out, "%d, ", list[i]);
    }
    fprintf(tl_out, "\n");
  } /*else {
    fprintf(tl_out, "Do not postpone\n");
  }*/
#endif

  int acc = tl_ltl3ba?check_if_acc_node(list):1;

  for(i = 1; i < list[0]; i++) {
    AProd *p;
    if (!transition[list[i]] || transition[list[i]]->empty()) {
      trans_exist = 0;
      break;
    }
    if ((postpone && in_set(INFp_nodes, list[i])) && 
        (postpone == 2 || !in_set(UXp_nodes, list[i]))) {
      p = new AProd(list[i], empty_t);
      p->merge_to_prod(prod->nxt, p->astate);
    } else {
      p = new AProd(list[i], transition[list[i]]);
      if (!p->trans) trans_exist = 0;
      else p->merge_to_prod(prod->nxt, *p->curr_trans);
    }
    p->nxt = prod->nxt;
    p->prv = prod;
    p->nxt->prv = p;
    p->prv->nxt = p;
  }

  while(trans_exist) { /* calculates all the transitions */
    AProd *p = prod->nxt;
    t1 = p->prod;
    t1_to = &p->prod_to;
    if(t1) { /* solves the current transition */
//      cGTrans trans;
      fin->clear();
/*    if (acc) {*/
/*      if (tl_ltl3ba && !compute_directly)
        substract_set(fin, final_set, t1->bad_nodes);
      else*/
        for(i = 1; i < final[0]; i++)
          if(is_final(s->nodes_set, t1, t1_to, final[i]))
            fin->insert(final[i]);

        if(postpone)
          fin->substract(t1->bad_nodes);
/*    }*/

      if((!tl_det_m && s->trans->check_dominance(t1, t1_to, fin, acc, state_trans, s)) ||
         (tl_det_m && s->trans->determinize(t1, t1_to, fin, acc, state_trans, s))) { /* adds the transition */
        if (tl_postpone) {
          if (UG_succ != NULL &&
              !empty_intersect_sets(is_UG, t1_to->get_set(), 0) &&
              !empty_intersect_sets(is_Gs, t1_to->get_set(), 0)) {
            int *set = intersect_sets(is_UG, t1_to->get_set(), 0);
            int ii, jj, mod = 8 * sizeof(int);

            for(ii = 0; ii < node_size; ii++) {
              for(jj = 0; jj < 8 * sizeof(int); jj++) {
                if(set[ii] & (1 << jj)) {
                  if(t1_to->is_elem(UG_succ[(mod * ii + jj) - 1]))
                    t1_to->erase(mod * ii + jj);
                }
              }
            }
            tfree(set);
          }
          if (tl_f_components && can_be_optimized(t1_to)) {
#if SUPP_OUT == YES
            printf("Yes: ");
#endif
            remove_redundand_targets(t1_to, fin);
#if SUPP_OUT == YES
            std::cout << t1_to;
            printf("\n");
#endif
          }
        }
        GState *to = find_gstate(t1_to, s);
//        std::cout << "Inserting trans to: " << to->id << std::endl;
        // if it is a new transition, incerement counters
        if (s->trans->add_trans(t1->label, fin, to)) {
          to->incoming++;
          state_trans++;
        }
      }
    }
    if(!p->trans)
      break;
    while(p->no_next()) /* calculates the next transition */ {
      p = p->nxt;
    }
    if(p == prod)
      break;
    p->next();
    if ((postpone && in_set(INFp_nodes, p->astate)) && 
        (postpone == 2 || !in_set(UXp_nodes, p->astate))) {
      p->merge_to_prod(p->nxt, p->astate);
    } else {
      p->merge_to_prod(p->nxt, *p->curr_trans);
    }
    p = p->prv;
    while(p != prod) {
      p->restart();
      if ((postpone && in_set(INFp_nodes, p->astate)) &&
          (postpone == 2 || !in_set(UXp_nodes, p->astate))) {
        p->merge_to_prod(p->nxt, p->astate);
      } else {
        p->merge_to_prod(p->nxt, *p->curr_trans);
      }
      p = p->prv;
    }
  }
  
  tfree(list); /* free memory */
  while(prod->nxt != prod) {
    AProd *p = prod->nxt;
    prod->nxt = p->nxt;
    delete p;
  }
  delete prod;

  if(!compute_directly && tl_simp_fly) {
    if(s->trans->empty()) { /* s has no transitions */
      delete s->trans;
      s->trans = (cGTrans *)0;
      s->prv = (GState *)0;
      s->nxt = gremoved->nxt;
      gremoved->nxt = s;
      for(s1 = gremoved->nxt; s1 != gremoved; s1 = s1->nxt)
        if(s1->prv == s)
        s1->prv = (GState *)0;
      return;
    }
    
    gstates->trans = s->trans;
    s1 = gstates->nxt;
    while(!all_gtrans_match(s, s1, 0))
      s1 = s1->nxt;
    if(s1 != gstates) { /* s and s1 are equivalent */
      s->trans->decrement_incoming();
      delete s->trans;
      s->trans = (cGTrans *)0;
      s->prv = s1;
      s->nxt = gremoved->nxt;
      gremoved->nxt = s;
      for(s1 = gremoved->nxt; s1 != gremoved; s1 = s1->nxt)
        if(s1->prv == s)
          s1->prv = s->prv;
      return;
    }
  }

  s->nxt = gstates->nxt; /* adds the current state to 'gstates' */
  s->prv = gstates;
  s->nxt->prv = s;
  gstates->nxt = s;
  gtrans_count += state_trans;
  gstate_count++;
}

/********************************************************************\
|*            Display of the generalized Buchi automaton            *|
\********************************************************************/

void reverse_print_generalized(GState *s) /* dumps the generalized Buchi automaton */
{
  if(s == gstates) return;

  reverse_print_generalized(s->nxt); /* begins with the last state */

  std::map<GState*, std::map<cset, bdd>, GStateComp>::iterator t;
  std::map<cset, bdd>::iterator t2;
  
  fprintf(tl_out, "state %i (", s->id);
  s->nodes_set->print();
  fprintf(tl_out, ") : %i\n", s->incoming);
    for(t = s->trans->begin(); t != s->trans->end(); t++) {
      for(t2 = t->second.begin(); t2 != t->second.end(); t2++) {
        if (t2->second == bdd_true()) {
          fprintf(tl_out, "(1)");
        } else {
          print_or = 0;
          bdd_allsat(t2->second, allsatPrintHandler);
        }
        fprintf(tl_out, " -> %i : ", t->first->id);
        t2->first.print();
        fprintf(tl_out, "\n");
      }
    }
}

void print_generalized() { /* prints intial states and calls 'reverse_print' */
  int i;
  fprintf(tl_out, "init :\n");
  for(i = 0; i < init_size; i++)
    if(init[i])
      fprintf(tl_out, "%i\n", init[i]->id);
  reverse_print_generalized(gstates->nxt);
}

void print_tgba_acc(int i) {
  fprintf(tl_out, " \"");
  dump(label[i]);
  fprintf(tl_out, "\"");
}

void print_tgba_acc_set(const cset& set) {
  int* list = set.to_list();
  int i;
  
  for(i = 1; i < list[0]; i++)
    print_tgba_acc(list[i]);
  
  tfree(list);
}

void print_tgba_state_name(const cset* set, bool is_hoaf) {
  int* list = set->to_list();
  int i;
  
  if (list[0] <= 1) {
    fprintf(tl_out, (is_hoaf ? "\"t\"" : "\"1\""));
  } else {
    fprintf(tl_out, "\"");
    for(i = 1; i < list[0];) {
     	dump(label[list[i]]);
     	i++;
     	if (i < list[0]) {
     	  fprintf(tl_out, " && ");
     	}
   	}
    fprintf(tl_out, "\"");
  }
}

void print_tgba_all_transitions_of(const GState* s) {
  std::map<GState*, std::map<cset, bdd>, GStateComp>::iterator t;
  std::map<cset, bdd>::iterator t2;

  for(t = s->trans->begin(); t != s->trans->end(); t++) {
    for(t2 = t->second.begin(); t2 != t->second.end(); t2++) {
      print_tgba_state_name(s->nodes_set, false);
      fprintf(tl_out, ", ");
      print_tgba_state_name(t->first->nodes_set, false);
      fprintf(tl_out, ", \"");
      if (t2->second == bdd_true()) {
        fprintf(tl_out, "1");
      } else {
        print_or = 0;
        bdd_allsat(t2->second, allsatPrintHandler);
      }
      fprintf(tl_out, "\",");

      print_tgba_acc_set(t2->first);
      fprintf(tl_out, ";\n");
    }
  }
}

void print_tgba() {
  int i;
  GState *s;
  
  fprintf(tl_out, "acc =");
  for(i = 1; i < final[0]; i++) {
    print_tgba_acc(final[i]);
  }
  fprintf(tl_out, ";\n");

  for (s = gstates->prv; s != gstates; s = s->prv)
    s->incoming = 0;

  if(init_size > 1) {
    fprintf(tl_out, "init =");
    for(i = 0; i < init_size; i++)
      if(init[i]) {
        fprintf(tl_out, " ");
        print_tgba_state_name(init[i]->nodes_set, false);
      }
    fprintf(tl_out, ";\n");
  }

  for(i = 0; i < init_size; i++) {
    if(init[i]) {
      print_tgba_all_transitions_of(init[i]);
      init[i]->incoming = 1;      
    }
  }

  for (s = gstates->prv; s != gstates; s = s->prv) {
    if (s->incoming == 0)
      print_tgba_all_transitions_of(s);
  }
}

void print_generalized_hoaf_acc_set(const cset& set,
                                    const std::map<int, int>& final2Int) {
  int *list = set.to_list();
  if (list[0] > 1)
    fprintf(tl_out, " {");
  for(int i = 1; i < list[0]; i++) {
    if (i > 1)
      fprintf(tl_out, " ");
    fprintf(tl_out, "%d", final2Int.find(list[i])->second);
  }
  if (list[0] > 1)
    fprintf(tl_out, "}");
  tfree(list);
}

void print_generalized_hoaf_header(int states,
                                   int init_states,
                                   const std::map<int, int>& final2Int,
                                   const std::map<GState*, int>& gstate2Int,
                                   const std::string& name) {
  fprintf(tl_out, "HOA: v1\n");
  fprintf(tl_out, "tool: \"ltl3ba\" \"%s\"\n", VERSION_NUM);
  fprintf(tl_out, "name: \"%s for ", name.c_str());
  put_uform();
  fprintf(tl_out, "\"\n");
  fprintf(tl_out, "States: %d\n", states);
  if (states > 0) {
    for(int i = 0; i < init_states; i++)
      if(init[i])
      fprintf(tl_out, "Start: %d\n", gstate2Int.find(init[i])->second);
    fprintf(tl_out, "acc-name: generalized-Buchi %u\n", final2Int.size());
    fprintf(tl_out, "Acceptance: %u", final2Int.size());
    if (final2Int.size() > 0) {
      for(std::map<int, int>::const_iterator i = final2Int.begin(); i != final2Int.end(); i++) {
        if (i != final2Int.begin())
          fprintf(tl_out, " &");
        fprintf(tl_out, " Inf(%d)", i->second);
      }
    } else {
      fprintf(tl_out, " t");
    }
    fprintf(tl_out, "\n");
    fprintf(tl_out, "AP: %d", predicates);
    for (int i = 0; i < predicates; ++i) {
      fprintf(tl_out, " \"%s\"", sym_table[i]);
    }
    fprintf(tl_out, "\n");
    fprintf(tl_out, "properties: trans-labels explicit-labels trans-acc no-univ-branch\n");
  } else {
    fprintf(tl_out, "acc-name: all\n");
    fprintf(tl_out, "Acceptance: 0 t\n");
  }
}

void print_generalized_hoaf(const std::string& name = "TGBA"){
  GState *s;
  std::map<GState*, std::map<cset, bdd>, GStateComp>::iterator t;
  std::map<cset, bdd>::iterator t2;
  std::map<int, int> final2Int;
  std::map<GState*, int> gstate2Int;
  
  gstate_count = 0;
  for(int i = 1; i < final[0]; i++) {
    final2Int[final[i]] = gstate_count++;
  }
  gstate_count = 0;
  for (s = gstates->prv; s != gstates; s = s->prv) {
    gstate2Int[s] = gstate_count++;
  }

  print_generalized_hoaf_header(gstate_count, init_size, final2Int, gstate2Int, name);

  fprintf(tl_out, "--BODY--\n");

  for(s = gstates->prv; s != gstates; s = s->prv) {
    fprintf(tl_out, "State: %d ", gstate2Int[s]);
    print_tgba_state_name(s->nodes_set, true);
    fprintf(tl_out, "\n");
    for(t = s->trans->begin(); t != s->trans->end(); t++) {
      for(t2 = t->second.begin(); t2 != t->second.end(); t2++) {
        fprintf(tl_out, " [");
        if (t2->second == bdd_true()) {
          fprintf(tl_out, "t");
        } else {
          print_or = 0;
          bdd_allsat(t2->second, allsatPrintHandler_hoaf);
        }
        fprintf(tl_out, "] %d", gstate2Int[t->first]);
        print_generalized_hoaf_acc_set(t2->first, final2Int);
        fprintf(tl_out, "\n");
      }
    }
  }
  fprintf(tl_out, "--END--\n");
}

void init_empty_t() {
  empty_t = new std::map<cset, ATrans*>();
  ATrans *t = emalloc_atrans();
  t->label = bdd_true();
  empty_t->insert(std::pair<cset, ATrans*>(cset(0), t));
}

/********************************************************************\
|*                       Main method                                *|
\********************************************************************/

void mk_generalized()
{ /* generates a generalized Buchi automaton from the alternating automaton */
  std::map<cset, ATrans*>::iterator t;
  GState *s;
  int i;

  fin = new cset(0);
  bad_scc = 0; /* will be initialized in simplify_gscc */
  final = list_set(final_set, 0);
  init_empty_t();

  gstack        = (GState *)tl_emalloc(sizeof(GState)); /* sentinel */
  gstack->nxt   = gstack;
  gremoved      = (GState *)tl_emalloc(sizeof(GState)); /* sentinel */
  gremoved->nxt = gremoved;
  gstates       = (GState *)tl_emalloc(sizeof(GState)); /* sentinel */
  gstates->nxt  = gstates;
  gstates->prv  = gstates;

  if (transition[0])
    for(t = transition[0]->begin(); t != transition[0]->end(); t++) { /* puts initial states in the stack */
      s = (GState *)tl_emalloc(sizeof(GState));
      s->id = (t->first.empty()) ? 0 : gstate_id++;
      s->incoming = 1;
      s->nodes_set = new cset(t->first);
      s->trans = new cGTrans();
      s->nxt = gstack->nxt;
      gstack->nxt = s;
#ifdef DICT
      gsDict.insert(std::pair<cset, GState*>(*s->nodes_set, s));
#endif
      init_size++;
    }

  if(init_size) init = (GState **)tl_emalloc(init_size * sizeof(GState *));
  init_size = 0;
  for(s = gstack->nxt; s != gstack; s = s->nxt)
    init[init_size++] = s;

/*    fprintf(tl_out, "\nINFp: ");
    for(i = 1; i < 24; i++) {
        if (in_set(INFp_nodes, i))
          fprintf(tl_out, "%d, ", i);
    }
    fprintf(tl_out, "\n");
    
    fprintf(tl_out, "UXp: ");
    for(i = 1; i < 24; i++) {
      if (in_set(UXp_nodes, i))
        fprintf(tl_out, "%d, ", i);
    }
    fprintf(tl_out, "\n\n");*/


  while(gstack->nxt != gstack) { /* solves all states in the stack until it is empty */
    s = gstack->nxt;
    gstack->nxt = gstack->nxt->nxt;
    if(!s->incoming) {
#ifdef DICT
      gsDict.erase(*s->nodes_set);
#endif
      free_gstate(s);
      continue;
    }
    make_gtrans(s);
  }

  retarget_all_gtrans();

#ifdef DICT
  gsDict.clear();
#endif

  tfree(gstack);
  free_atrans_map(empty_t);
  for(i = 0; i < node_id; i++) /* frees the data from the alternating automaton */
    free_atrans_map(transition[i]);
  free_all_atrans();
  tfree(transition);

  if(tl_verbose) {
    fprintf(tl_out, "Generalized Buchi automaton before simplification\n");
    if (tl_verbose == 1)
      print_generalized();
    else
      print_generalized_hoaf();
    fprintf(tl_out, "\n");
  }

  if(tl_simp_diff) {
    if (tl_simp_scc) simplify_gscc();
    simplify_gtrans();
    if (tl_simp_scc) simplify_gscc();
    while(simplify_gstates()) { /* simplifies as much as possible */
      if (tl_simp_scc) simplify_gscc();
      simplify_gtrans();
      if (tl_simp_scc) simplify_gscc();
    }
    
    if(tl_verbose) {
      fprintf(tl_out, "Generalized Buchi automaton after simplification\n");
      if (tl_verbose == 1)
        print_generalized();
      else
        print_generalized_hoaf();
      fprintf(tl_out, "\n");
    }
  }
  
  if(tl_hoaf == 2) {
    print_generalized_hoaf();
    tfree(label);
  } else if(tl_spot_out == 2) {
    print_tgba();
    tfree(label);
  }
  tfree(predecessors);
}
  
