/***** ltl3dra : dra.c *****/

/* Written by Tomas Babiak and Frantisek Blahoudek                        */
/*                                                                        */
/* Based on paper by                                                      */
/* T. Babiak, F. Blahoudek, M. Kretinsky, and J. Strejcek                 */
/* Effective Translation of LTL to Deterministic Rabin Automata:          */
/* Beyond the (F,G)-Fragment (2013)                                       */
/* In 11th International Symposium on Automated Technology for            */
/* Verification and Analysis (ATVA 2013)                                  */

#include <queue>
/*#include "ltl3dra.h"*/
#include "dra.h"
#include <bdd.h>
#include <map>
#include <set>
#include <list>


#define NO 0
#define YES 1
/* Define whether to use supplementary outputs or not. */
#define SUPP_OUT NO

/* When defined, auxiliary dictionaries are used to speed up searching */
/* among existing states.             Comment to disable.              */
#define DICT

using namespace dra;

/********************************************************************\
|*              Structures and shared variables                     *|
\********************************************************************/

extern FILE *tl_out;
extern std::map<cset, ATrans*> **transition;

//extern int tl_simp_fly, tl_ltl3ba, tl_f_components, compute_directly;
extern int tl_verbose, tl_spot_out, tl_hoaf, tl_dra_ltl2dstar, tl_fjtofj, print_or, sym_id, *final_set, *final,
  *must_nodes, *may_nodes, **predecessors, tl_dra_opt, tl_dra_acc_imp, tl_simp_diff,
  tl_dra_conf_dom, predicates;
extern char **sym_table;
static std::ostream* where_os;

extern GState *gremoved, *gstates;
#ifdef DICT
extern std::map<cset, GState*> gsDict;
#endif
extern int gstate_id;
extern cset *fin;
extern std::string uform;

std::set<DRAstate*, DRAstateComp> drastates;
std::set<DRAstate*, DRAstateComp> draRemoved;
DRAstate* dra_init;
std::queue<DRAstate*> draqueue;
int DRAstate_id = 1;
int dra::DRAtrans_id = 1;
std::list<bdd> det_constraints;

extern std::set<cset> Z_set;
std::map<cset, int> Z_setToInt;
std::map<int, cset> IntToZ_set;
std::map<int, std::pair<int,int> > Zindex_to_hoaf;
std::map<int, int> acc_to_pos;
std::map<int, int> pos_to_acc;
std::map<int, std::set<cset> > ACz;  // Allowed configurations for given Z-index?
int hoaf_acc_count = 0;
std::map<DRAstate*, int> state2Int; // Maps TGDRA states to their HOAF id

typedef std::vector<std::vector<bool> > inclusionTable_t; // if inclusionTable_t[i][j]=true -> i \subseteq j
std::vector<inclusionTable_t> condSubsets;
std::vector<cset> removedI_sets;

typedef std::pair<bool, std::vector<bool> > condSetFlag_t;
std::vector<condSetFlag_t> condSethasTrans;
std::vector<bool> isRemoved;
int removedConds = 0;

inclusionTable_t implicationTable; // if implicationTable[i][j]=true -> i => j
std::vector<std::vector<std::vector<cset> > > potentialSubsetsCache;

void print_generalized();
GState* get_gstate_and_trans(const cset& set);

/********************************************************************\
|*        Implementation of some methods of auxiliary classes       *|
\********************************************************************/

bool are_F_successors(cset& Fs, cset& sucs) {
  int *list = sucs.to_list();

  for (int i = 1; i < list[0]; i++) {
    if (empty_intersect_sets(predecessors[list[i]], Fs.get_set(), 0)) {
      if (list)
        tfree(list);
      return false;
    }
  }

  if (list)
    tfree(list);
  return true;
}

void DRAstate::insert(cset &c) {

//  Incorrect antichain-optimization disabled. Uncomment to enable.
//  std::set<cset>::iterator i,j;
//  cset Fs, temp;
//  for (i=sets.begin(); i!=sets.end();) {
//    if (i->is_subset_of(c)) {
//      Fs.intersect_sets(*i, may_nodes);
//      if (!Fs.empty()) {
//        temp.substract(c, *i);
//        if (are_F_successors(Fs, temp))
//          i++;
//        else
//          return;
//      } else
//        return;
//    } else if (c.is_subset_of(*i)) {
//      j = i++;
//      Fs.intersect_sets(c, may_nodes);
//      if (!Fs.empty()) {
//        temp.substract(*j, c);
//        if (!are_F_successors(Fs, temp))
//          sets.erase(j);
//      } else
//        sets.erase(j);
//    } else {
//      i++;
//    }

  sets.insert(c);
}

void DRAstate::insert_transition(bdd label, DRAstate* to) const {
  std::map<DRAstate*, DRAtrans>::iterator t = trans->find(to);
  if (t == trans->end()) {
    trans->insert(std::make_pair(to, DRAtrans(label, this, to)));
    to->incoming++;
  } else {
    t->second.insert_label(this, label);
  }
}

// If there is already trans with same cond, merge the labeles
// Otherwise add new trans
void DRAtrans::insert_label(const DRAstate* from, bdd l) {
  GenCondMap_t cond = evaluate_acc_cond(from, l);
  std::map<GenCondMap_t, bdd>::iterator t = conds_to_labels.find(cond);
  if (t == conds_to_labels.end()) {
    conds_to_labels.insert(std::make_pair(cond, l));
  } else {
    t->second |= l;
  }
}

void DRAtrans::remove_redundant_acc_conds(const std::list<int>& toBeRemoved) {
  std::map<GenCondMap_t, bdd>::iterator m_j, t;
  std::list<int>::const_iterator l_i;

  std::map<GenCondMap_t, bdd> newCondsAndLabels;

  for (m_j = conds_to_labels.begin(); m_j != conds_to_labels.end(); m_j++) {
    GenCondMap_t tempConds = m_j->first;
    for (l_i = toBeRemoved.begin(); l_i != toBeRemoved.end(); l_i++) {
      tempConds.erase(*l_i);
    }

    t = newCondsAndLabels.find(tempConds);
    if (t == newCondsAndLabels.end()) {
      newCondsAndLabels.insert(std::make_pair(tempConds, m_j->second));
    } else {
      t->second |= m_j->second;
    }

    newCondsAndLabels.insert(std::make_pair(tempConds, m_j->second));
  }

  conds_to_labels.swap(newCondsAndLabels);
}

/********************************************************************\
|*                     Accepting conditions                         *|
\********************************************************************/

int is_final(const cset& from, bdd label, cset to, int i) /*is the transition final for i ?*/
{
  std::map<cset, ATrans*>::iterator t;
//  int in_to;
/*  if((tl_fjtofj && !to.is_elem(i)) ||
    (!tl_fjtofj && !from.is_elem(i))) return 1;
*/
//  in_to = to.is_elem(i);
  to.erase(i);
  for(t = transition[i]->begin(); t != transition[i]->end(); t++)
    if(t->first.is_subset_of(to) &&
       ((t->second->label << label) == bdd_true())) {
//      if(in_to) to.insert(i);
      return 1;
    }
//  if(in_to) to.insert(i);
  return 0;
}

GenCond DRAtrans::allowed_for_Z(int i, const DRAstate* from, bdd label) {
  std::set<cset>::iterator m_j, m_k;
  std::map<GState*, std::map<cset, bdd>, GStateComp>::iterator t_i;
  cset acc;
  GenCond c(final[0]-1);
  c.allowed = false;

  std::vector<bool>* flag;
  if (tl_dra_opt)
    flag = &condSethasTrans[i-1].second;

  /* Searches for an allowed configuration such that it has a multitransition
   * into allowed configuration of the target macrostate (to) of this transition */

  // Use c_1 (m_j) from AC_Z
  for (m_j = ACz[i].begin(); m_j != ACz[i].end(); m_j++) {
    if (!tl_dra_acc_imp) {
      // Check whether c_1 \in m_1 \cup AC_Z
      if (from->sets.find(*m_j) == from->sets.end()) {
        continue;
      }
    }

    // Creates a state of TGBA for the configuration c_1 (m_j)
    GState *gs = get_gstate_and_trans(*m_j);

    // The set of may states of c_1
    acc.intersect_sets(*m_j, final_set);

    // Check all multitransitions going from c_1
    for (t_i = gs->trans->begin(); t_i != gs->trans->end(); t_i++) {
      // Check whether the labels agree
      bdd l = t_i->second.begin()->second;
      if ((l << label) == bdd_true()) {
        // Check whether current multitransition (t_i) leads
        // to an allowed configuration
        if ((m_k = ACz[i].find(*(t_i->first)->nodes_set)) != ACz[i].end()) {
          // Check whether the current multitransition (t_i) leads
          // to an configuration of "to" macrostate
          if (to->sets.find(*m_k) != to->sets.end()) {
            c.allowed = true;
            // Check whether the multitransition is f-accepting
            if (!acc.empty()) {
              int *list = acc.to_list();
              for (int j = 1; j < list[0]; j++) {
                if(is_final(*m_j, label, *m_k, list[j])) {
                  c.f_accepting[acc_to_pos[list[j]]] = true;
                  if (tl_dra_opt)
                    (*flag)[acc_to_pos[list[j]]] = true;
                }
              }
              if (list)
                tfree(list);
            }
          }
        }
      }
    }
  }

  if (tl_dra_opt && c.allowed) {
    condSethasTrans[i-1].first = true;

    // compute inclusion on conditions
    std::vector<bool>::size_type j, k;
    for (j = 0; j < c.f_accepting.size(); j++) {
      for (k = j+1; k < c.f_accepting.size(); k++) {
        if (c.f_accepting[j] && !c.f_accepting[k]) {
          // j is not a subset of k
          condSubsets[i-1][j][k] = false;
        } else if (!c.f_accepting[j] && c.f_accepting[k]) {
          // k is not a subset of j
          condSubsets[i-1][k][j] = false;
        }
      }
    }
  }

  return c;
}

// Checks whether \forall j \in J \exists i \in I so that I_i \subseteq I_j holds.
// Therefore, if \exists j \in J \forall i \in I such that I_i \not\subseteq I_j it is violated and return false.
bool evaluate_subsets_for_implication(std::vector<cset>& subsets, std::vector<bool>& f_acc1, std::vector<bool>& f_acc2, int Z_2) {
  int i, *list;
  std::vector<bool>::size_type j;
  cset& c = IntToZ_set[Z_2];

  // subset[j] stores the set of all I_i's for which there is a chance that I_i \subseteq I_j

  // If J is empty than it hols trivially
  if (c.size() == 0)
    return true;

  // Go over all I_j (search for the righ one)
  for (j = 0; j < f_acc2.size(); j++) {
    // If this transition is not in I_j (f_acc2[j] is false)
    if (!f_acc2[j] && c.is_elem(pos_to_acc[j])) {
      // Check remaining I_j if this transition is also not there
      list = subsets[j].to_list();
      for(i = 1; i < list[0]; i++) {
        // If this transition is in I_i then I_i can not be subseteq of this I_j
        if (f_acc1[acc_to_pos[list[i]]]) {
          // so remove it from subset[i]
          subsets[j].erase(list[i]);
        }
      }

      if (list)
        tfree(list);

      // If no I_i's left then I_i \not\subseteq I_j for all i \in I
      if (subsets[j].empty()) {
        // Therefore, \exists j \in J \forall i \in I such that I_i \not\subseteq I_j so return false
        return false;
      }
    }
  }
  return true;
}

GenCondMap_t DRAtrans::evaluate_acc_cond(const DRAstate* from, bdd label) {
  std::set<cset>::iterator m_i;

  // We return the cond object. The cond object maps the indices of gen. Rabin pairs into info,
  // in which of the pair's sets the transition (this with the given 'bdd label') is.
  GenCondMap_t cond;

  // First init the cond object
  for (m_i = Z_set.begin(); m_i != Z_set.end(); m_i++) {
    int i = Z_setToInt[*m_i];
    cond.insert(std::make_pair(i, allowed_for_Z(i, from, label)));
  }

  if (tl_dra_opt && !cond.empty()) {
    GenCondMap_t::iterator m_i, m_j;
    for (m_i = cond.begin(); m_i != --cond.end(); m_i++) {
      for (m_j = m_i, m_j++; m_j != cond.end(); m_j++) {
        if (m_i->second.allowed && !m_j->second.allowed) {
          // F_j cannot be subset of F_i therefore \neg(Z_i => Z_j)
          implicationTable[m_i->first-1][m_j->first-1] = false;
        } else if (!m_i->second.allowed && m_j->second.allowed) {
          // F_i cannot be subset of F_j therefore \neg(Z_j => Z_i)
          implicationTable[m_j->first-1][m_i->first-1] = false;
        } else {
          // F_i and F_j are OK on this transition, check I_i's and I_j's
          if (implicationTable[m_i->first-1][m_j->first-1]) {
            // It is still possible that Z_i => Z_j so check that still
            // \forall j \in J \exists i \in I so that I_i can be subset of I_j
            implicationTable[m_i->first-1][m_j->first-1] =
              evaluate_subsets_for_implication(potentialSubsetsCache[m_i->first-1][m_j->first-1],
                                                 m_i->second.f_accepting, m_j->second.f_accepting, m_j->first);
          }
          if (implicationTable[m_j->first-1][m_i->first-1]) {
            // It is still possible that Z_j => Z_i so check that still
            // \forall i \in I \exists j \in J so that I_j can be subset of I_i
            implicationTable[m_j->first-1][m_i->first-1] =
              evaluate_subsets_for_implication(potentialSubsetsCache[m_j->first-1][m_i->first-1],
                                                 m_j->second.f_accepting, m_i->second.f_accepting, m_i->first);
          }
        }
      }
    }
  }

  return cond;
}

void compute_allowed_conf() {
  std::set<cset>::iterator s_i, s_j;
  int *list, i, j = 1;
  cset hoaf_acc;
  cset must, may;

  for (s_i = Z_set.begin(); s_i != Z_set.end(); s_i++) {
    Z_setToInt.insert(std::make_pair(*s_i, j));
    IntToZ_set.insert(std::make_pair(j, *s_i));
    hoaf_acc.intersect_sets(*s_i, final_set);
    int inf_sets = (hoaf_acc).size();
    Zindex_to_hoaf.insert(std::make_pair(j,std::make_pair(hoaf_acc_count,inf_sets)));
    hoaf_acc_count += inf_sets + 1;
    must.intersect_sets(*s_i, must_nodes);
    may.substract(*s_i, must);
    list = may.to_list();

    //DEBUG
    //std::cout << j << ":" << *s_i << std::endl;
    //std::cout << hoaf_acc_count << "," << inf_sets << std::endl;
    //END DEBUG

    std::set<cset> s_1, s_2;
    s_1.insert(must);

    for(i=1; i < list[0]; i++) {
      for(s_j=s_1.begin(); s_j!=s_1.end(); s_j++) {
        s_2.insert(*s_j);
        cset s_temp(*s_j);
        s_temp.insert(list[i]);
        s_2.insert(s_temp);
      }
      s_1.swap(s_2);
      s_2.clear();
    }

    if (list)
      tfree(list);

    ACz.insert(std::make_pair(j, s_1));
    j++;
  }
}

/********************************************************************\
|*        Generation of the generalized Buchi automaton             *|
\********************************************************************/

GState* dra::find_gstate(cset *set, GState *s)
{ /* finds the corresponding state, or creates it */

//  if(tl_f_components && compute_directly) return s;

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
  s->nxt = gstates->nxt;
  gstates->nxt = s;
#ifdef DICT
  // Insert a new state into dictionary
//  gsDict.insert(std::pair<cset, GState*>(*s->nodes_set, s));
  *st_temp = s;
#endif
  return s;
}

void dra::make_gtrans(GState *s) { /* creates all the transitions from a state */
  int i, *list, trans_exist = 1;
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

  for(i = 1; i < list[0]; i++) {
    AProd *p;
    p = new AProd(list[i], transition[list[i]]);
    if (!p->trans) trans_exist = 0;
    else p->merge_to_prod(prod->nxt, *p->curr_trans);
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

      GState *to = find_gstate(t1_to, s);
      if (s->trans->add_trans(t1->label, fin, to)) {
        to->incoming++;
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

    p->merge_to_prod(p->nxt, *p->curr_trans);
    p = p->prv;
    while(p != prod) {
      p->restart();
      p->merge_to_prod(p->nxt, *p->curr_trans);
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
}

/********************************************************************\
|*        Generation of the generalized Rabin automaton             *|
\********************************************************************/

DRAstate* find_drastate(DRAstate* s) {
  std::pair<std::set<DRAstate*,DRAstateComp>::iterator, bool> ret;

  ret = drastates.insert(s);
  if (ret.second) {
      s->id = DRAstate_id++;
      draqueue.push(s);
  } else {
    delete s;
  }

//  s = (DRAstate *)0;
  return *(ret.first);
}

std::list<bdd> prepare_det_constraints() {
  int i;
  bdd a;

  std::list<bdd> l_1, l_2;
  std::list<bdd>::iterator j;
  l_1.push_back(bdd_true());

//  for(i=0; i<sym_id; i++) { CHANGE of order due to ltl2dstar output
  for(i=sym_id-1; i>=0; i--) {
    a = bdd_ithvar(i);
    for(j=l_1.begin(); j!=l_1.end(); j++) {
      l_2.push_back(*j&a);
      l_2.push_back(*j&!a);
    }
    l_1.swap(l_2);
    l_2.clear();
  }

  return l_1;
}

GState* get_gstate_and_trans(const cset& set) {
  GState **gs = &gsDict[set];
  if (*gs == NULL) {
    *gs = (GState *)tl_emalloc(sizeof(GState)); /* creates a new state */
    (*gs)->id = (set.empty()) ? 0 : gstate_id++;
    (*gs)->incoming = 0;
    (*gs)->nodes_set = new cset(set);
    (*gs)->trans = new cGTrans();
    (*gs)->nxt = gstates->nxt;
    gstates->nxt = (*gs);
  }
  if ((*gs)->trans->empty())
    make_gtrans(*gs);

  return (*gs);
}

void make_DRAtrans(const DRAstate* s) {
  std::set<cset>::iterator c_x, c_y, c_z, c_i;
  std::list<bdd>::iterator l_i;

  std::map<GState*, std::map<cset, bdd>, GStateComp>::iterator t_i;

  cset temp,acc;

  for(l_i=det_constraints.begin(); l_i!=det_constraints.end(); l_i++) {
    DRAstate *prod_to = new DRAstate();
    bool empty_flag = false;

    // For every configuration find successor configurations under label l_i
    for(c_x = s->sets.begin(); c_x != s->sets.end(); c_x++) {
      GState *gs = get_gstate_and_trans(*c_x);
      std::set<cset> sets, toRemove;

      for (t_i = gs->trans->begin(); t_i != gs->trans->end(); t_i++) {
        bdd label = t_i->second.begin()->second & *l_i;
        if (label != bdd_false()) {
          temp = *t_i->first->nodes_set;
          //  Empty configuration test
          if (temp.empty()) {
            sets.clear();
            sets.insert(temp);
            empty_flag = true;
            break;
          }

          //is needed? -- antichain alternative
          if(tl_dra_conf_dom) {
            bool needed_flag = true;
            for(c_y = sets.begin(); c_y != sets.end(); c_y++) {

              if(needed_flag) {
              // Is temp dominated by c_y?
                if(c_y->is_subset_of(temp)) {
                  needed_flag = false;
                  acc.intersect_sets(*c_x, may_nodes);
                  if(!acc.empty()) {
                    int *list = acc.to_list();
                    for (int j = 1; j < list[0]; j++) {
                    if(is_final(*c_x, *l_i, temp, list[j]) && !is_final(*c_x, *l_i, *c_y, list[j])) {
                        needed_flag = true;
                      }
                    }
                    if (list)
                         tfree(list);
                    if(!needed_flag)
                      break;
                  }
                } else

                // Does temp dominate some other configuration?
                if(temp.is_subset_of(*c_y)) {
                  bool erase_y_flag = true;
                  acc.intersect_sets(*c_x, may_nodes);
                if(!acc.empty()) {
                  int *list = acc.to_list();
                  for (int j = 1; j < list[0]; j++) {
                    if(is_final(*c_x, *l_i, *c_y, list[j]) && !is_final(*c_x, *l_i, temp, list[j])) {
                        erase_y_flag = false;
                      }
                    }
                    if (list)
                         tfree(list);
                }
                if(erase_y_flag) {
                    sets.erase(*c_y);
                }
              }
            }
          }
          if(!needed_flag)
              continue;
          }

          sets.insert(temp);
        }
      }

//      // Check what configurations can be left out
//      for(c_y = sets.begin(); c_y != sets.end(); c_y++) {
//        c_z = c_y;
//        c_z++;
//        for(; c_z != sets.end(); c_z++) {
//          // Z is dominated by y
//          if(c_y->is_subset_of(*c_z)) {
//            bool erase_z_flag = true;
//            acc.intersect_sets(*c_x, may_nodes);
//            if(!acc.empty()) {
//              int *list = acc.to_list();
//              for (int j = 1; j < list[0]; j++) {
//                if(is_final(*c_x, *l_i, *c_z, list[j]) && !is_final(*c_x, *l_i, *c_y, list[j])) {
//                  erase_z_flag = false;
//                }
//              }
//              if (list)
//                     tfree(list);
//            }
//            if(erase_z_flag) {
//                toRemove.insert(*c_z);
//            }
//          } else
//          if(c_z->is_subset_of(*c_y)) {
//            bool erase_y_flag = true;
//            acc.intersect_sets(*c_x, may_nodes);
//            if(!acc.empty()) {
//              int *list = acc.to_list();
//              for (int j = 1; j < list[0]; j++) {
//                if(is_final(*c_x, *l_i, *c_y, list[j]) && !is_final(*c_x, *l_i, *c_z, list[j])) {
//                  erase_y_flag = false;
//                }
//              }
//              if (list)
//                     tfree(list);
//            }
//            if(erase_y_flag) {
//                toRemove.insert(*c_y);
//            }
//          }
//        }
//      }

//      for(c_i = toRemove.begin(); c_i != toRemove.end();c_i++) {
//        sets.erase(*c_i);
//      }

      for(c_i = sets.begin(); c_i != sets.end(); c_i++) {
        temp = *c_i;
        prod_to->insert(temp);
      }
      if(empty_flag) {break;}
    }

    // Additional "antichain" check. Don't care about the parent
    // configuration if no self-loops were used
//    if (tl_dra_conf_dom) {
//      for(c_y = prod_to->sets.begin();c_y != prod_to->sets.end();c_y++) {
//        bool no_selfloop = false;
//        acc.intersect_sets(*c_y,may_nodes);
//        if(acc.empty()) {
//          no_selfloop = true;
//        } else {
//          for(c_x = s->sets.begin(); c_x != s->sets.end(); c_x++) {
//            GState *gs = get_gstate_and_trans(*c_x);
//            bool is_parent = false;
//            for (t_i = gs->trans->begin(); t_i != gs->trans->end(); t_i++) {
//              bdd label = t_i->second.begin()->second & *l_i;
//              if (label != bdd_false()) {
//                temp = *t_i->first->nodes_set;
//                if(temp == *c_y) {
//                  is_parent = true;
//                  break;
//                }
//              }
//            }
//            if(is_parent) {
//            acc.intersect_sets(*c_x,may_nodes);
//            int *list = acc.to_list();
//            for (int j = 1; j < list[0]; j++) {
//              if(!is_final(*c_x, *l_i, *c_y, list[j])) {
//                  break;
//                }
//              no_selfloop = true;
//            }
//            if (list)
//                 tfree(list);
//            if(no_selfloop)
//              break;
//            }
//          }
//        }
//        if(no_selfloop) {
//          c_z = c_y;
//          c_z++;
//          std::vector<cset> toRem;
//          for(; c_z != prod_to->sets.end();c_z++) {
//            if(c_y->is_subset_of(*c_z))
//              toRem.push_back(*c_z);
//          }
//          for(c_z = prod_to->sets.begin(); c_z != c_y;c_z++) {
//            if(c_y->is_subset_of(*c_z))
//              toRem.push_back(*c_z);
//          }
//          for(int i = 0; i<toRem.size();i++)
//            prod_to->sets.erase(toRem[i]);
//        }
//      }
//    }

    DRAstate *to = find_drastate(prod_to);
    s->insert_transition(*l_i, to);
  }
}

/********************************************************************\
|*        Simplification of the generalized Rabin automaton         *|
\********************************************************************/

void remove_redundant_acc_conds(std::list<int>& toBeRemoved) {
  //toBeRemoved is a list of Z-indices, started by 1.

  // Erase the acc condition from transitions
  std::set<DRAstate*, DRAstateComp>::iterator s_i;
  std::map<DRAstate*, DRAtrans>::iterator t_i;

  for(s_i=drastates.begin(); s_i!=drastates.end(); s_i++) {
    for(t_i=(*s_i)->trans->begin(); t_i!=(*s_i)->trans->end(); t_i++) {
      t_i->second.remove_redundant_acc_conds(toBeRemoved);
    }
  }

  // Update the information for HOAF output
  std::list<int>::iterator z_i;
  std::map<int, std::pair<int, int> >::iterator hz_i;

  for(z_i = toBeRemoved.begin(); z_i != toBeRemoved.end(); z_i++) {
    for(hz_i = Zindex_to_hoaf.begin(); hz_i != Zindex_to_hoaf.end(); hz_i++) {
        if (hz_i->first <= *z_i)
          continue;
        (hz_i->second).first -= Zindex_to_hoaf[*z_i].second + 1;
    }
    hoaf_acc_count -= Zindex_to_hoaf[*z_i].second + 1;
    Zindex_to_hoaf.erase(*z_i);
  }
}

bool evaluate_condSetFlag(condSetFlag_t& flag, const cset&c) {
  std::vector<std::vector<bool> >::size_type i;

  if (!flag.first)
    return true;

  for (i = 0; i < flag.second.size(); i++) {
    if (c.is_elem(pos_to_acc[i]) && !flag.second[i])
      return true;
  }

  return false;
}

bool evaluate_implicationTable(std::vector<std::vector<bool> >::size_type i) {
  std::vector<std::vector<bool> >::size_type j;
  for (j=0; j<implicationTable.size(); j++) {
    if (implicationTable[i][j] && j!=i &&
        // Checks that converse does not hold or
        // the second condition has not been removed yet
        // so we don't remove both in case of i=>j and j=>i
        (!implicationTable[j][i] || !isRemoved[j]))
      return true;
  }
  return false;
}

// Removes useless I_k of condition (F, I_1,...,I_k,...,I_j)
void remove_redundant_acc_I_sets() {
  int I_j, I_k;
  std::vector<std::vector<bool> >::size_type i;
  cset fin_states;
  for (i = 0; i<Z_set.size(); i++) {
    if (!isRemoved[i]) {
      fin_states.intersect_sets(IntToZ_set[i+1], final_set);
      if (fin_states.size() > 1) {
        int* list = fin_states.to_list();
        for (int j = 1; j < list[0]-1; j++) {
          I_j = acc_to_pos[list[j]];
          for (int k = j+1; k < list[0]; k++) {
            I_k = acc_to_pos[list[k]];
            if (condSubsets[i][I_j][I_k] ) {
              // I_j \subseteq I_k -> I_k can be removed
              removedI_sets[i].insert(list[k]);
              //DEBUG
              //std::cout << "remove1" << I_k << std::endl;
            } else if (condSubsets[i][I_k][I_j]) {
              if (removedI_sets[i].is_elem(list[k]))
                 continue;
              // I_k \subseteq I_j -> I_j can be removed
              removedI_sets[i].insert(list[j]);
              //DEBUG
              //std::cout << "remove2" << I_j << std::endl;
            }
          }
        }
        if (list)
          tfree(list);
      }
      // Update the information for HOAF output

      //DEBUG
      //std::cout << removedI_sets[i].size() << " vs. " << removed_for_this_Z << std::endl;
      //END DEBUG

      // For HOAF we have to decrease the set numbers acording to the removed sets.
      int removed_for_this_Z = removedI_sets[i].size();
      Zindex_to_hoaf[i+1].second -= removed_for_this_Z;
      //DEBUG
      //std::cout << i+1 << ":" << removed_for_this_Z << std::endl;
      //END DEBUG

      for(auto hz_i = Zindex_to_hoaf.begin(); hz_i != Zindex_to_hoaf.end(); hz_i++) {
          if (hz_i->first <= i+1)
            continue;
          (hz_i->second).first -= removed_for_this_Z;
      }
      hoaf_acc_count -= removed_for_this_Z;
    }
  }
}

bool all_dratrans_match(DRAstate *s1, DRAstate *s2) {
  std::map<DRAstate*, DRAtrans>::iterator m_1, m_2;

  if (s1->trans->size() != s2->trans->size())
    return false;

  m_1 = s1->trans->begin();
  m_2 = s2->trans->begin();

  for (; m_1 != s1->trans->end(); m_1++, m_2++) {
    if (m_1->first != m_2->first|| m_1->second != m_2->second)
      return false;
  }

  return true;
}

void decrement_incoming(std::map<DRAstate*, DRAtrans> *trans) {
  std::map<DRAstate*, DRAtrans>::iterator t;
  for(t = trans->begin(); t != trans->end(); t++)
      t->first->incoming--;
}

void remove_drastate(DRAstate *s, DRAstate *sub) {
  std::set<DRAstate*, DRAstateComp>::iterator s_i;

  decrement_incoming(s->trans);
  delete s->trans;
  s->trans = (std::map<DRAstate*, DRAtrans>*) 0;

  s->sub = sub;
  for (s_i = draRemoved.begin(); s_i != draRemoved.end(); s_i++)
    if ((*s_i)->sub == s)
      (*s_i)->sub = sub;
  draRemoved.insert(s);
}

void retarget_all_dratrans() {
  std::set<DRAstate*, DRAstateComp>::iterator s_i;
  std::map<DRAstate*, DRAtrans>::iterator t_i, t_temp;
  std::map<DRAstate*, DRAtrans>* trans;
  std::map<GenCondMap_t, bdd>::iterator m_i;

  if (draRemoved.size() == 0)
    return;

  if (!dra_init->trans)
    dra_init = dra_init->sub; // dra_init has been removed -> replace it

  for (s_i = drastates.begin(); s_i != drastates.end(); s_i++) {
    trans = (*s_i)->trans;
    for (t_i = trans->begin(); t_i != trans->end(); ) {
      if (!t_i->first->trans && // t->to has been removed
           t_i->first->sub) { // t->to has substitute -> retarget transition there
        DRAtrans t = t_i->second;
        t.to = t_i->first->sub;
        t_temp = t_i;
        t_i++;
        if (trans->find(t.to) == trans->end()) {
          // transition to t.to state does not exist -> create a new one
          trans->insert(std::make_pair(t.to, t));
          t.to->incoming++;
        } else {
          // transition to t.to state does exist -> update it
          DRAtrans *t1 = &(trans->find(t.to)->second);
          for (m_i = t.conds_to_labels.begin(); m_i != t.conds_to_labels.end(); m_i++) {
            bdd *l = &((t1->conds_to_labels)[m_i->first]);
            if (*l == bdd_false()) {
              *l = m_i->second;
            } else {
              *l |= m_i->second;
            }
          }
        }
        // erase the old transition (the one going to a removed state)
        trans->erase(t_temp);
      } else {
        t_i++;
      }
    }
  }

  for (s_i = draRemoved.begin(); s_i != draRemoved.end(); s_i++) {
    delete *s_i;
  }
  draRemoved.clear();
}

void simplify_drastates() {
  bool removed = false;
  std::set<DRAstate*, DRAstateComp>::iterator s_i, s_j, s_temp;

  do {
    for(s_i = drastates.begin(); s_i != drastates.end(); s_i++) {
//      if(s_i->trans->empty()) { // s_i has no transitions
//        remove_drastate(s_i, (DRAstate *)0);
//        s_temp = s_i;
//        s_i++;
//        drastates.erase(s_temp);
//        continue;
//      }

      s_j = s_i;
      for (s_j++; s_j != drastates.end();) {
        if(all_dratrans_match(*s_i, *s_j)) { // s_i and s_j are equivalent
          remove_drastate(*s_j, *s_i);
          s_temp = s_j;
          s_j++;
          drastates.erase(s_temp);
        } else {
          s_j++;
        }
      }
    }

    if (draRemoved.size() > 0) {
      removed = true;
      retarget_all_dratrans();
    } else {
      removed = false;
    }
  } while (removed);
}

void remove_redundant_dra_init() {
  if (dra_init->incoming == 0) {
    std::map<DRAstate*, DRAtrans>::iterator m_x, m_y;
    for (m_x=dra_init->trans->begin(); m_x!=dra_init->trans->end(); m_x++) {
      DRAstate *s = m_x->first;
      if (s == dra_init)
          continue;

      if (dra_init->trans->size() != s->trans->size())
        continue;

      for (m_y=dra_init->trans->begin(); m_y!=dra_init->trans->end(); m_y++) {
        DRAstate *to = m_y->first;
        DRAtrans *t1 = &m_y->second;
        std::map<DRAstate*, DRAtrans>::iterator m_z = s->trans->find(to);
        if (m_z == s->trans->end())
          break;

        DRAtrans *t2 = &m_z->second;

        bdd label_t1 = bdd_false();
        bdd label_t2 = bdd_false();

        std::map<GenCondMap_t, bdd>::iterator m_i, m_j;
        for (m_i=t1->conds_to_labels.begin(); m_i!=t1->conds_to_labels.end(); m_i++) {
          label_t1 |= m_i->second;
        }
        for(m_j=t2->conds_to_labels.begin(); m_j!=t2->conds_to_labels.end(); m_j++) {
          label_t2 |= m_j->second;
        }

        if (label_t1 != label_t2) {
          break;
        }
      }

      if (m_y==dra_init->trans->end()) {
        // Delete old initial state
        drastates.erase(dra_init);
        decrement_incoming(dra_init->trans);
        delete dra_init;
        // Set new initial state
        dra_init = s;
        remove_redundant_dra_init();
        return;
      }
    }
  }
}

/********************************************************************\
|*            Display of the generalized Rabin automaton            *|
\********************************************************************/

std::ostream& dra::operator<<(std::ostream &out, const DRAstate &r) {
  std::set<cset>::iterator i;
  std::cout << "\"[";
  for (i = r.sets.begin(); i != r.sets.end(); i++) {
    if (i != r.sets.begin())
      out << ", ";
    out << *i;
  }
  out << "]\"";
  return out;
}

std::ostream& dra::operator<<(std::ostream &out, const GenCond &c) {
  std::vector<bool>::const_iterator it;
//
  out << "<" << (c.allowed?"+":"-") << ",{";
  for (it = c.f_accepting.begin(); it != c.f_accepting.end(); it++) {
    if (it != c.f_accepting.begin())
      out << ",";
    out << (*it?"+":"-");
  }
  out << "}>";
  return out;
}

void GenCond::print(std::ostream &out, int Z_i) const {
  bool start = true;
  cset& z_set = IntToZ_set[Z_i];

  out << "<" << (allowed?"+":"-") << ",{";
  std::vector<bool>::size_type i;
  for (i = 0; i < f_accepting.size(); i++) {
    if (z_set.is_elem(pos_to_acc[i]) &&
        (!tl_dra_opt || !removedI_sets[Z_i-1].is_elem(pos_to_acc[i]) ) ) {
      if (!start)
        out << ",";
      out << (f_accepting[i]?"+":"-");
      start = false;
    }
  }
  out << "}>";
}

bool GenCond::print_hoaf(std::ostream &out, int Z_i, bool first) const {
  int f_counter = 0;
  cset& z_set = IntToZ_set[Z_i];

  if (!allowed) {
    if (!first) {out << " ";}
    if (first)  {out << "{"; first = false;}
    out << Zindex_to_hoaf[Z_i].first;
  }
  std::vector<bool>::size_type i;
  for (i = 0; i < f_accepting.size(); i++) {
    // Choose only the f-states for which I_Z,f is defined
    // I.e. f \in Z, I_f was not removed due optimizations
    if (z_set.is_elem(pos_to_acc[i]) &&
        (!tl_dra_opt || !removedI_sets[Z_i-1].is_elem(pos_to_acc[i]) ) ) {
      ++f_counter;
      if (f_accepting[i]) {
        if (!first) {out << " ";}
        if (first)  {out << "{"; first = false;}
        out << Zindex_to_hoaf[Z_i].first + f_counter;
      }
    }
  }
  return first;
}

/* OLD OUTPUT TRANS*/
/*std::ostream& dra::operator<<(std::ostream &out, const DRAtrans &t) {
  where_os = &out;
  std::map<GenCondMap_t, bdd>::const_iterator m_j;

  // Each item of conds_to_labels represents an edge. Print the edges.
  for (m_j = t.conds_to_labels.begin(); m_j != t.conds_to_labels.end(); m_j++) {
    out << "\t";
    print_or = 0;
    bdd label = m_j->second;

    if (label == bdd_true())
      out << "(1)";
    else
      bdd_allsat(label, allsatPrintHandler);
    out << " -> " << t.to->id << "\t";

    GenCondMap_t::const_iterator z_i;
    for(z_i=m_j->first.begin(); z_i!=m_j->first.end(); z_i++) {
      if (z_i != m_j->first.begin())
        out << ", ";
      out << z_i->first << ":";
      z_i->second.print(out, z_i->first);
    }
    out << std::endl;
  }

  return out;
}*/

std::ostream& dra::operator<<(std::ostream &out, const DRAtrans &t) {
  where_os = &out;
  std::map<GenCondMap_t, bdd>::const_iterator m_j;

  //Print HOAF
  if (tl_verbose == 2 || tl_hoaf > 1) {
    // Each item of conds_to_labels represents an edge. Print the edges.
    for (m_j = t.conds_to_labels.begin(); m_j != t.conds_to_labels.end(); m_j++) {
      out << "\n  [";
      where_os = &out;
      print_or = 0;
      bdd label = m_j->second;

      if (label == bdd_true())
        out << "t";
      else
        bdd_allsat(label, allsatPrintHandler_hoaf);
      out << "] " << state2Int[t.to] << " ";

      GenCondMap_t::const_iterator z_i;
      bool first_acc = true;
      for(z_i=m_j->first.begin(); z_i!=m_j->first.end(); z_i++) {
        first_acc = z_i->second.print_hoaf(out, z_i->first,first_acc);
      }
      if (!first_acc)
        out << "}";
    }
  }
  // Print in the ltl3dra v0.1 format
  else {
    for (m_j = t.conds_to_labels.begin(); m_j != t.conds_to_labels.end(); m_j++) {
      out << "\t";
      print_or = 0;
      bdd label = m_j->second;

      if (label == bdd_true())
        out << "(1)";
      else
        bdd_allsat(label, allsatPrintHandler);
      out << " -> " << t.to->id << "\t";

      GenCondMap_t::const_iterator z_i;
      for(z_i=m_j->first.begin(); z_i!=m_j->first.end(); z_i++) {
        if (z_i != m_j->first.begin())
          out << ", ";
        out << z_i->first << ":";
        z_i->second.print(out, z_i->first);
      }
      out << std::endl;
    }
  }
  return out;
}

void print_tgdra_hoaf_header(int states,
                             std::map<DRAstate*, int>& state2Int,
                             const std::map<int, std::pair<int, int> >& Zindex_to_hoaf,
                             const std::string& name = "TGDRA"
                             ) {
  std::cout << "HOA: v1";
  std::cout << "\ntool: \"ltl3dra\" \"" << VERSION_NUM << "\"";
  std::cout << "\nname: \"" << name << " for " << uform << "\"";
  std::cout << "\nStates: " << states;
  if (states > 0) {
    std::cout << "\nStart: " << state2Int[dra_init];
    std::cout << "\nacc-name: generalized-Rabin " << Zindex_to_hoaf.size();
    for(std::map<int, std::pair<int, int> >::const_iterator i = Zindex_to_hoaf.begin(); i != Zindex_to_hoaf.end(); i++) {
      std::cout << " " << (i->second).second;
    }
    std::cout << "\nAcceptance: " << hoaf_acc_count ;
    if (Zindex_to_hoaf.size()>0) {
      for(std::map<int, std::pair<int, int> >::const_iterator i = Zindex_to_hoaf.begin(); i != Zindex_to_hoaf.end(); i++) {
        if (i != Zindex_to_hoaf.begin())
          std::cout << " |";
        std::cout << " (Fin(" << (i->second).first << ")";
        for (int j = 1; j <= (i->second).second; ++j) {
          std::cout << "&Inf(" << (i->second).first + j << ")";
        }
        std::cout << ")";
      }
    } else {
      std::cout << " f";
    }
    std::cout << "\nAP: " << predicates;
    for (int i = 0; i < predicates; ++i) {
      std::cout << " \"" << sym_table[i] << "\"";
    }
    std::cout << "\nproperties: deterministic trans-labels explicit-labels trans-acc no-univ-branch";
  } else {
    std::cout << "\nacc-name: none";
    std::cout << "\nAcceptance: 0 f";
  }
}


void print_dra_hoaf(std::ostream &out, const std::string& name = "") {
  std::set<DRAstate*, DRAstateComp>::iterator s_i;
  std::map<DRAstate*, DRAtrans>::iterator t_i;

  state2Int.clear();
  // Create the mapping from TGDRAstates to their HOAF id.
  int state_count = 0;
  for(s_i=drastates.begin(); s_i!=drastates.end(); s_i++) {
    state2Int[*s_i] = state_count++;
  }
  // Print the hoaf header
  if (name != "") {
    print_tgdra_hoaf_header(state_count,state2Int,Zindex_to_hoaf,name);
  } else {
    print_tgdra_hoaf_header(state_count,state2Int,Zindex_to_hoaf);
  }

  out << "\n--BODY--";
  // Print states and their transitions
  for(s_i=drastates.begin(); s_i!=drastates.end(); s_i++) {
    out << "\nState: " << state2Int[*s_i] << " " << *(*s_i);
    for(t_i=(*s_i)->trans->begin(); t_i!=(*s_i)->trans->end(); t_i++) {
      out << t_i->second;
    }
  }
  out << "\n--END--" << std::endl;
}

void print_dra_old(std::ostream &out) {
  std::set<DRAstate*, DRAstateComp>::iterator s_i;
  std::map<DRAstate*, DRAtrans>::iterator t_i;

  out << "Init: " << dra_init->id << std::endl;
  for(s_i=drastates.begin(); s_i!=drastates.end(); s_i++) {
    out << "state " << (*s_i)->id << ": " << *(*s_i) << std::endl;
    for(t_i=(*s_i)->trans->begin(); t_i!=(*s_i)->trans->end(); t_i++) {
      out << t_i->second;
    }
  }
}

/********************************************************************\
|*                       Main method                                *|
\********************************************************************/

void mk_dra() {
  std::map<cset, ATrans*>::iterator t;
  GState *s;
  fin = new cset(0); // default condition set used for TGBA transitions
  final = list_set(final_set, 0);

  gremoved      = (GState *)tl_emalloc(sizeof(GState)); /* sentinel */
  gremoved->nxt = gremoved;
  gstates       = (GState *)tl_emalloc(sizeof(GState)); /* sentinel */
  gstates->nxt  = gstates;
  gstates->prv  = gstates;

  det_constraints = prepare_det_constraints();
  compute_allowed_conf();
  for (int i = 1; i < final[0]; i++) {
    acc_to_pos[final[i]] = i-1;
    pos_to_acc[i-1] = final[i];
  }

  if (tl_dra_opt) {
    condSetFlag_t tempFlag = std::make_pair(false, std::vector<bool>(final[0]-1, false));
    condSethasTrans.resize(Z_set.size(), tempFlag);
    isRemoved.resize(Z_set.size(), false);

    int f_states = final[0]-1;
    inclusionTable_t tempTable = inclusionTable_t(f_states, std::vector<bool>(f_states, true));
    condSubsets.resize(Z_set.size(), tempTable);
    removedI_sets.resize(Z_set.size(), cset(0));

    implicationTable.resize(Z_set.size(),std::vector<bool>(Z_set.size(),true));
    cset temp_set;
    std::vector<bool>::size_type i;
    for (i = 0; i<Z_set.size(); i++) {
      temp_set.intersect_sets(IntToZ_set[i+1], final_set);
      std::vector<std::vector<cset> > tempSubsets(Z_set.size(), std::vector<cset>(f_states, temp_set));
      potentialSubsetsCache.push_back(tempSubsets);
    }
  }

  if (transition[0])
    for(t = transition[0]->begin(); t != transition[0]->end(); t++) { /* puts initial states in the stack */
      s = (GState *)tl_emalloc(sizeof(GState));
      s->id = (t->first.empty()) ? 0 : gstate_id++;
      s->incoming = 1;
      s->nodes_set = new cset(t->first);
      s->trans = new cGTrans();
      s->nxt = gstates->nxt;
      gstates->nxt = s;
#ifdef DICT
      gsDict.insert(std::pair<cset, GState*>(*s->nodes_set, s));
#endif
    }


  dra_init = new DRAstate(DRAstate_id++);
  for(s = gstates->nxt; s != gstates; s = s->nxt) {
    dra_init->insert(*s->nodes_set);
  }
  drastates.insert(dra_init);
  draqueue.push(dra_init);

  while(!draqueue.empty()) { /* solves all states in the stack until it is empty */
    const DRAstate* dra = draqueue.front();
    draqueue.pop();

    make_DRAtrans(dra);
  }

  if (gremoved->nxt != gremoved)
    std::cerr << "Error: Undefined behaviour -- states in gremoved std::queue!!!\n";

#if SUPP_OUT == YES
  fprintf(tl_out, "\nGen automaton\n");
  print_generalized();
#endif

  if (tl_verbose == 1) {
    std::cout << "\nCo-buchi accepting states:\n{";
    for (int i = 1; i < final[0]; i++) {
      if (i != 1)
        std::cout << ", ";
      std::cout << final[i];
    }
    std::cout << "}\n\n";
  }

  if (tl_verbose == 1) {
    std::set<cset>::iterator s_i;
    std::cout << "Z_set:\n";
    for (s_i = Z_set.begin(); s_i != Z_set.end(); s_i++) {
      if (s_i != Z_set.begin())
        std::cout << ", ";
      std::cout << Z_setToInt[*s_i] << ":";
      s_i->print_and_mark(std::cout, final_set);
    }
    std::cout << std::endl;
  }

#if SUPP_OUT == YES
  std::map<int, std::set<cset> >::iterator m_i;
  std::set<cset>::iterator s_i;
  std::cout << "ACz:\n";
  for (m_i = ACz.begin(); m_i != ACz.end(); m_i++) {
    if (m_i != ACz.begin())
      std::cout << ", ";
    std::cout << "<" << m_i->first << ", [";
    for (s_i = m_i->second.begin(); s_i != m_i->second.end(); s_i++) {
      if (s_i != m_i->second.begin())
        std::cout << ", ";
      std::cout << *s_i;
    }
    std::cout << "]>";
  }
  std::cout << std::endl;
#endif

  remove_redundant_dra_init();

  // Print the implicationTable
//  std::cout << "\nImplicationTable.size: " << implicationTable.size() << std::endl;
//  for (int i=0; i<implicationTable.size(); i++) {
//    for (int j=0; j<implicationTable.size(); j++) {
//      std::cout << implicationTable[i][j] << " ";
//    }
//    std::cout << std::endl;
//  }


  if (tl_verbose && (tl_dra_opt || tl_simp_diff)) {
    if (tl_verbose == 1) {
      std::cout << std::endl << "TGDRA before simplification" << std::endl;
      print_dra_old(std::cout);
      std::cout << std::endl << "TGDRA after simplification" << std::endl;
    }
    if (tl_verbose == 2) print_dra_hoaf(std::cout,"TGDRA before simplification");
  }

  if (tl_dra_opt) {

    std::list<int> toBeRemoved;

    std::vector<bool>::size_type i;
    for (i = 0; i < Z_set.size(); i++) {
      if (evaluate_condSetFlag(condSethasTrans[i], IntToZ_set[i+1]) ||
          evaluate_implicationTable(i)) {
        toBeRemoved.push_back(i+1);
        isRemoved[i] = true;
      }
    }

    if (toBeRemoved.size() > 0) {
      remove_redundant_acc_conds(toBeRemoved);

      // Save number of removed acc_conds for output of the number of acc_conds
      removedConds = toBeRemoved.size();
    }

    // Removes useless I_k of condition (F, I_1,...,I_k,...,I_j)
    remove_redundant_acc_I_sets();

  }

  if(tl_simp_diff) {
    simplify_drastates();
    remove_redundant_dra_init();
  }

  if (tl_verbose == 1 || tl_spot_out == 2) {
    print_dra_old(std::cout);
  }

  if (tl_verbose == 2 || tl_hoaf == 2) {
    print_dra_hoaf(std::cout,"TGDRA");
  }
}
