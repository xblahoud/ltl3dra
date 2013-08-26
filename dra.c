/***** ltl3ba : dra.c *****/

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

using namespace std;
using namespace dra;

/********************************************************************\
|*              Structures and shared variables                     *|
\********************************************************************/

extern FILE *tl_out;
extern map<cset, ATrans*> **transition;
#ifdef STATS
extern struct rusage tr_debut, tr_fin;
extern struct timeval t_diff;
#endif
//extern int tl_simp_fly, tl_ltl3ba, tl_f_components, compute_directly;
extern int tl_verbose, tl_fjtofj, print_or, sym_id, *final_set, *final,
  *must_nodes, *may_nodes, **predecessors, tl_dra_opt, tl_dra_acc_imp, tl_simp_diff,
  tl_dra_conf_dom;
extern char **sym_table;
static std::ostream* where_os;

extern GState *gremoved, *gstates;
#ifdef DICT
extern map<cset, GState*> gsDict;
#endif
extern int gstate_id;
extern cset *fin;

set<DRAstate*, DRAstateComp> drastates;
set<DRAstate*, DRAstateComp> draRemoved;
DRAstate* dra_init;
queue<DRAstate*> draqueue;
int DRAstate_id = 1;
int dra::DRAtrans_id = 1;
list<bdd> det_constraints;

extern set<cset> Z_set;
map<cset, int> Z_setToInt;
map<int, cset> IntToZ_set;
map<int, int> acc_to_pos;
map<int, int> pos_to_acc;
map<int, set<cset> > ACz;

typedef vector<vector<bool> > inclusionTable_t; // if inclusionTable_t[i][j]=true -> i \subseteq j
vector<inclusionTable_t> condSubsets;
vector<cset> removedI_sets;

typedef pair<bool, vector<bool> > condSetFlag_t;
vector<condSetFlag_t> condSethasTrans;
vector<bool> isRemoved;
int removedConds = 0;

inclusionTable_t implicationTable; // if implicationTable[i][j]=true -> i => j
vector<vector<vector<cset> > > potentialSubsetsCache;

void print_generalized();
GState* get_gstate_and_trans(const cset& set);

/********************************************************************\
|*        Implementation of some methods of auxiliary classes       *|
\********************************************************************/

bool are_F_successors(cset& Fs, cset& sucs) {
  int *list = sucs.to_list();
  int i;
  
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

//  Antichains optimization disabled. Uncomment to enable.
//  set<cset>::iterator i,j;
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
  map<DRAstate*, DRAtrans>::iterator t = trans->find(to);
  if (t == trans->end()) {
    trans->insert(make_pair(to, DRAtrans(label, this, to)));
    to->incoming++;
  } else {
    t->second.insert_label(this, label);
  }
}

// If there is already trans with same cond, merge the labeles
// Otherwise add new trans
void DRAtrans::insert_label(const DRAstate* from, bdd l) {
  GenCondMap_t cond = evaluate_acc_cond(from, l);
  map<GenCondMap_t, bdd>::iterator t = conds_to_labels.find(cond);
  if (t == conds_to_labels.end()) {
    conds_to_labels.insert(make_pair(cond, l));
  } else {
    t->second |= l;
  }
}

void DRAtrans::remove_redundant_acc_conds(const list<int>& toBeRemoved) {
  map<GenCondMap_t, bdd>::iterator m_j, t;
  list<int>::const_iterator l_i;
  
  map<GenCondMap_t, bdd> newCondsAndLabels;

  for (m_j = conds_to_labels.begin(); m_j != conds_to_labels.end(); m_j++) {
    GenCondMap_t tempConds = m_j->first;
    for (l_i = toBeRemoved.begin(); l_i != toBeRemoved.end(); l_i++) {
      tempConds.erase(*l_i);
    }

    t = newCondsAndLabels.find(tempConds);
    if (t == newCondsAndLabels.end()) {
      newCondsAndLabels.insert(make_pair(tempConds, m_j->second));
    } else {
      t->second |= m_j->second;
    }

    newCondsAndLabels.insert(make_pair(tempConds, m_j->second));
  }
  
  conds_to_labels.swap(newCondsAndLabels);
}

/********************************************************************\
|*                     Accepting conditions                         *|
\********************************************************************/

int is_final(const cset& from, bdd label, cset to, int i) /*is the transition final for i ?*/
{
  map<cset, ATrans*>::iterator t;
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
  set<cset>::iterator m_j, m_k;
  std::map<GState*, std::map<cset, bdd>, GStateComp>::iterator t_i;
  cset acc;
  GenCond c(final[0]-1);
  c.allowed = false;

  vector<bool>* flag;
  if (tl_dra_opt)
    flag = &condSethasTrans[i-1].second;

  /* Searches for allowed configuration such that it has multitransition
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
    int j, k;
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
bool evaluate_subsets_for_implication(vector<cset>& subsets, vector<bool>& f_acc1, vector<bool>& f_acc2, int Z_2) {
  int i, j, *list;
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
  set<cset>::iterator m_i;
  GenCondMap_t cond;

  for (m_i = Z_set.begin(); m_i != Z_set.end(); m_i++) {
    int i = Z_setToInt[*m_i];
    cond.insert(make_pair(i, allowed_for_Z(i, from, label)));
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
  set<cset>::iterator s_i, s_j;
  int *list, i, j = 1;
  cset must, may;
  
  for (s_i = Z_set.begin(); s_i != Z_set.end(); s_i++) {
    Z_setToInt.insert(make_pair(*s_i, j));
    IntToZ_set.insert(make_pair(j, *s_i));
    must.intersect_sets(*s_i, must_nodes);
    may.substract(*s_i, must);
    list = may.to_list();

    set<cset> s_1, s_2;
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
    
    ACz.insert(make_pair(j, s_1));
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
/*  map<cset, GState*>::iterator gs_temp = gsDict.find(*set);
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
//  gsDict.insert(pair<cset, GState*>(*s->nodes_set, s));
  *st_temp = s;
#endif
  return s;
}

void dra::make_gtrans(GState *s) { /* creates all the transitions from a state */
  int i, *list, trans_exist = 1;
  GState *s1;
  ATrans *t1; /* *free, */
  cset *t1_to;
  AProd *prod = new AProd(); /* initialization */
  prod->nxt = prod;
  prod->prv = prod;
  list = s->nodes_set->to_list();

//  cout << endl << "Spracuvam stav: " << s->id << " s->nodes_set: " << *s->nodes_set << endl;

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
  pair<set<DRAstate*,DRAstateComp>::iterator, bool> ret;

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

list<bdd> prepare_det_constraints() {
  int i;
  bdd a;  

  list<bdd> l_1, l_2;
  list<bdd>::iterator j;
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
  int i, trans_exist = 1;
  set<cset>::iterator c_x, c_y, c_z, c_i;
  list<bdd>::iterator l_i;

  std::map<GState*, std::map<cset, bdd>, GStateComp>::iterator t_i;

  cset temp,acc;

  for(l_i=det_constraints.begin(); l_i!=det_constraints.end(); l_i++) {
    DRAstate *prod_to = new DRAstate();
    bool empty_flag = false;

    // For every configuration find successor configurations under label l_i
    for(c_x = s->sets.begin(); c_x != s->sets.end(); c_x++) {
      GState *gs = get_gstate_and_trans(*c_x);
      set<cset> sets, toRemove;

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
//          vector<cset> toRem;
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

void remove_redundant_acc_conds(list<int>& toBeRemoved) {
  set<DRAstate*, DRAstateComp>::iterator s_i;
  map<DRAstate*, DRAtrans>::iterator t_i;
  
  for(s_i=drastates.begin(); s_i!=drastates.end(); s_i++) {
    for(t_i=(*s_i)->trans->begin(); t_i!=(*s_i)->trans->end(); t_i++) {
      t_i->second.remove_redundant_acc_conds(toBeRemoved);
    }
  }
}

bool evaluate_condSetFlag(condSetFlag_t& flag, const cset&c) {
  int i;
  
  if (!flag.first)
    return true;
 
  for (i = 0; i < flag.second.size(); i++) {
    if (c.is_elem(pos_to_acc[i]) && !flag.second[i])
      return true;
  }
  
  return false;
}

bool evaluate_implicationTable(int i) {
  for (int j=0; j<implicationTable.size(); j++) {
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
  int i, j, k, I_j, I_k;
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
            } else if (condSubsets[i][I_k][I_j]) {
              // I_k \subseteq I_j -> I_j can be removed
              removedI_sets[i].insert(list[j]);
            }
          }
        }
        if (list)
          tfree(list);
      }
    }
  }
}

bool all_dratrans_match(DRAstate *s1, DRAstate *s2) {
  map<DRAstate*, DRAtrans>::iterator m_1, m_2;

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

void decrement_incoming(map<DRAstate*, DRAtrans> *trans) {
  map<DRAstate*, DRAtrans>::iterator t;
  for(t = trans->begin(); t != trans->end(); t++)
      t->first->incoming--;
}

void remove_drastate(DRAstate *s, DRAstate *sub) {
  set<DRAstate*, DRAstateComp>::iterator s_i;

  decrement_incoming(s->trans);
  delete s->trans;
  s->trans = (map<DRAstate*, DRAtrans>*) 0;
  
  s->sub = sub;
  for (s_i = draRemoved.begin(); s_i != draRemoved.end(); s_i++)
    if ((*s_i)->sub == s)
      (*s_i)->sub = sub;
  draRemoved.insert(s);
}

void retarget_all_dratrans() {
  set<DRAstate*, DRAstateComp>::iterator s_i;
  map<DRAstate*, DRAtrans>::iterator t_i, t_temp;
  map<DRAstate*, DRAtrans>* trans;
  map<GenCondMap_t, bdd>::iterator m_i;

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
          trans->insert(make_pair(t.to, t));
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
  set<DRAstate*, DRAstateComp>::iterator s_i, s_j, s_temp;

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
    map<DRAstate*, DRAtrans>::iterator m_x, m_y;
    for (m_x=dra_init->trans->begin(); m_x!=dra_init->trans->end(); m_x++) {
      DRAstate *s = m_x->first;
      if (s == dra_init)
          continue;
      
      if (dra_init->trans->size() != s->trans->size())
        continue;
      
      for (m_y=dra_init->trans->begin(); m_y!=dra_init->trans->end(); m_y++) {
        DRAstate *to = m_y->first;
        DRAtrans *t1 = &m_y->second;
        map<DRAstate*, DRAtrans>::iterator m_z = s->trans->find(to);
        if (m_z == s->trans->end())
          break;

        DRAtrans *t2 = &m_z->second;
        
        bdd label_t1 = bdd_false();
        bdd label_t2 = bdd_false(); 
          
        map<GenCondMap_t, bdd>::iterator m_i, m_j;
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
        return;
      }
    }
  }
}

/********************************************************************\
|*            Display of the generalized Rabin automaton            *|
\********************************************************************/

//void allsatPrintHandlerDRA(char* varset, int size)
//{
//  int print_and = 0;
//  
//  if (print_or) *where_os << " || ";
//  *where_os << "(";
//  for (int v=0; v<size; v++)
//  {
//    if (varset[v] < 0) continue;       
//    if (print_and) *where_os << " && ";
//    if (varset[v] == 0)
////      *where_os << "!(" << sym_table[v] << ")";
//      *where_os << "!" << sym_table[v];
//    else
////      *where_os << "(" << sym_table[v] << ")";
//      *where_os << sym_table[v];
//    print_and = 1;
//  }
//  *where_os << ")";
//  print_or = 1;
//}

std::ostream& dra::operator<<(std::ostream &out, const DRAstate &r) {
  set<cset>::iterator i;
  cout << "[";
  for (i = r.sets.begin(); i != r.sets.end(); i++) {
    if (i != r.sets.begin())
      out << ", ";
    out << *i;
  }
  out << "]";
  return out;
}


std::ostream& dra::operator<<(std::ostream &out, const GenCond &c) {
  vector<bool>::const_iterator it;

  out << "<" << (c.allowed?"+":"-") << ",{";
  for (it = c.f_accepting.begin(); it != c.f_accepting.end(); it++) {
    if (it != c.f_accepting.begin())
      out << ",";
    out << (*it?"+":"-");
  }
  out << "}>";
}

void GenCond::print(std::ostream &out, int Z_i) const {
  int i;
  bool start = true;
  cset& c = IntToZ_set[Z_i];

  out << "<" << (allowed?"+":"-") << ",{";
  for (i = 0; i < f_accepting.size(); i++) {
    if (c.is_elem(pos_to_acc[i]) &&
        (!tl_dra_opt || !removedI_sets[Z_i-1].is_elem(pos_to_acc[i]))) {
      if (!start)
        out << ",";
      out << (f_accepting[i]?"+":"-");
      start = false;
    }
  }
  out << "}>";
}

std::ostream& dra::operator<<(std::ostream &out, const DRAtrans &t) {
  where_os = &out;
  map<GenCondMap_t, bdd>::const_iterator m_j;

  for (m_j = t.conds_to_labels.begin(); m_j != t.conds_to_labels.end(); m_j++) {
    out << "\t";
    print_or = 0;
    bdd label = m_j->second;

    if (label == bdd_true())
      out << "(1)";
    else
      bdd_allsat(label, allsatPrintHandler);
    out << " -> " << t.to->id << "\t";

    GenCondMap_t::const_iterator m_i;
    for(m_i=m_j->first.begin(); m_i!=m_j->first.end(); m_i++) {
      if (m_i != m_j->first.begin())
        out << ", ";
      out << m_i->first << ":";
      m_i->second.print(out, m_i->first);
    }
    out << endl;
  }
  
  return out;
}

void print_dra(std::ostream &out) {
  set<DRAstate*, DRAstateComp>::iterator s_i;
  map<DRAstate*, DRAtrans>::iterator t_i;
  
  out << "Init: " << dra_init->id << endl;
  for(s_i=drastates.begin(); s_i!=drastates.end(); s_i++) {
    out << "state " << (*s_i)->id << " : " << *(*s_i) << endl;
    for(t_i=(*s_i)->trans->begin(); t_i!=(*s_i)->trans->end(); t_i++) {
      out << t_i->second;
    }
  }
}

/********************************************************************\
|*                       Main method                                *|
\********************************************************************/

void mk_dra() {
  map<cset, ATrans*>::iterator t;
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
    condSetFlag_t tempFlag = make_pair(false, vector<bool>(final[0]-1, false));
    condSethasTrans.resize(Z_set.size(), tempFlag);
    isRemoved.resize(Z_set.size(), false);
    
    int f_states = final[0]-1;
    inclusionTable_t tempTable = inclusionTable_t(f_states, vector<bool>(f_states, true));
    condSubsets.resize(Z_set.size(), tempTable);
    removedI_sets.resize(Z_set.size(), cset(0));
    
    implicationTable.resize(Z_set.size(),vector<bool>(Z_set.size(),true));
    cset temp_set;
    for (int i = 0; i<Z_set.size(); i++) {
      temp_set.intersect_sets(IntToZ_set[i+1], final_set);
      vector<vector<cset> > tempSubsets(Z_set.size(), vector<cset>(f_states, temp_set));
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
      gsDict.insert(pair<cset, GState*>(*s->nodes_set, s));
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
    cerr << "Error: Undefined behaviour -- states in gremoved queue!!!\n";

#if SUPP_OUT == YES  
  fprintf(tl_out, "\nGen automaton\n");
  print_generalized();
#endif
  
  if (tl_verbose) {
    cout << "\nCo-buchi accepting states:\n{";
    for (int i = 1; i < final[0]; i++) {
      if (i != 1)
        cout << ", ";
      cout << final[i];
    }
    cout << "}\n\n";
  }
  
  if (tl_verbose) {
    set<cset>::iterator s_i;
    cout << "Z_set:\n";
    for (s_i = Z_set.begin(); s_i != Z_set.end(); s_i++) {
      if (s_i != Z_set.begin())
        cout << ", ";
      cout << Z_setToInt[*s_i] << ":";
      s_i->print_and_mark(cout, final_set);
    }
    cout << endl;
  }

#if SUPP_OUT == YES
  map<int, set<cset> >::iterator m_i;
  set<cset>::iterator s_i;
  cout << "ACz:\n";
  for (m_i = ACz.begin(); m_i != ACz.end(); m_i++) {
    if (m_i != ACz.begin())
      cout << ", ";
    cout << "<" << m_i->first << ", [";
    for (s_i = m_i->second.begin(); s_i != m_i->second.end(); s_i++) {
      if (s_i != m_i->second.begin())
        cout << ", ";
      cout << *s_i;
    }
    cout << "]>";
  }
  cout << endl;
#endif

  remove_redundant_dra_init();

  // Print the implicationTable
//  cout << "\nImplicationTable.size: " << implicationTable.size() << endl;
//  for (int i=0; i<implicationTable.size(); i++) {
//    for (int j=0; j<implicationTable.size(); j++) {
//      cout << implicationTable[i][j] << " ";
//    }
//    cout << endl;
//  }


  if (tl_verbose && (tl_dra_opt || tl_simp_diff)) {
    fprintf(tl_out, "\nDRA automaton before optimization\n");
    print_dra(cout);
  }

  if (tl_dra_opt) {
    
    list<int> toBeRemoved;
    
    for (int i = 0; i < Z_set.size(); i++) {
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

  if (tl_verbose) {
    fprintf(tl_out, "\nDRA automaton\n");
    print_dra(cout);
  }
}

