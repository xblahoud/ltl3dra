/***** ltl3dra : ra.c *****/

/* Written by Tomas Babiak and Frantisek Blahoudek                        */
/*                                                                        */
/* Based on paper by                                                      */
/* T. Babiak, F. Blahoudek, M. Kretinsky, and J. Strejcek                 */
/* Effective Translation of LTL to Deterministic Rabin Automata:          */
/* Beyond the (F,G)-Fragment (2013)                                       */
/* In 11th International Symposium on Automated Technology for            */
/* Verification and Analysis (ATVA 2013)                                  */

#include <fstream>
#include <queue>
#include "ra.h"
#include <bdd.h>
#include <map>
#include <list>
#include <set>

/* When defined, auxiliary dictionaries are used to speed up searching */
/* among existing states.             Comment to disable.              */
#define DICT

using namespace dra;

/********************************************************************\
|*              Structures and shared variables                     *|
\********************************************************************/

extern int tl_verbose, tl_hoaf, tl_spot_out, tl_dra_ltl2dstar, print_or, *final_set, *final, tl_dra_opt, tl_simp_diff,
tl_dra_goal, tl_dra_stats,
predicates;
static std::ostream* where_os;
static std::ostream* gout;

extern FILE *tl_out;
extern std::string uform;

// GOAL output
extern std::ostream *goal_output;
extern std::ofstream *automaton;
extern char** sym_table;
extern int sym_id;
int from, to, tid = 0;
extern std::list<bdd> det_constraints;


extern std::set<cset> Z_set;
extern std::map<cset, int> Z_setToInt;
extern std::map<int, cset> IntToZ_set;
extern std::map<int, std::pair<int,int> > Zindex_to_hoaf;
extern std::map<int, int> acc_to_pos;
extern std::map<int, int> pos_to_acc;

extern std::set<DRAstate*, DRAstateComp> drastates;
extern DRAstate* dra_init;

std::vector<int> accept_levels;
std::vector<int*> finals_lists;
int levels_num;

std::set<RAstate*, RAstateComp> rastates;
std::set<RAstate*, RAstateComp> raRemoved;
RAstate* ra_init;
std::queue<RAstate*> raqueue;
int RAstate_id = 1;
int dra::RAtrans_id = 1;

extern std::vector<cset> removedI_sets;
extern std::vector<bool> isRemoved;
extern int removedConds;

// HOAF and ltl2dstar output
std::map<int,RAstate*> dstarMap;
std::map<int,int> id2dstar;
std::map<RAstate*,int> rastate2Int;
extern std::map<DRAstate*,int> state2Int;

std::list<RAstate*> init_copies;

/********************************************************************\
|*        Implementation of some methods of auxiliary classes       *|
\********************************************************************/

void RAstate::insert_transition(bdd label, RAstate* to) const {
  std::map<RAstate*, RAtrans>::iterator t = trans->find(to);
  if (t == trans->end()) {
    trans->insert(std::make_pair(to, RAtrans(label, to)));
    to->incoming++;
  } else {
    t->second.insert_label(label);
  }
}

/********************************************************************\
|*              Generation of the Rabin automaton                   *|
\********************************************************************/

RAstate *find_rastate(RAstate* s) {
  std::pair<std::set<RAstate*,RAstateComp>::iterator, bool> ret;

  ret = rastates.insert(s);
  if (ret.second) {
    s->id = RAstate_id++;
    raqueue.push(s);
    if (s->d_state->id == ra_init->d_state->id) {
      init_copies.push_back(s);
    }
  } else {
    delete s;
  }

  return *(ret.first);
}

int next_level(const GenCond &cond, int level, int accept, int* f_list) /* computes the 'final' value */
{
  if (!cond.allowed)
    return -1;
    
  if (level == -1)
    level = 0;
  
  while ((level != accept) && cond.f_accepting[acc_to_pos[f_list[level + 1]]])
    level++;
    
  return level;
}

std::vector<int> next_levels(const GenCondMap_t& conds, const std::vector<int>& old_levels) {
  int i;
  std::vector<int> levels(levels_num, 0);

  for (i = 0; i < levels_num; i++) {
    // Skip removed conditions
    if (tl_dra_opt && isRemoved[i])
      continue;
    int old_level = (old_levels[i] == accept_levels[i]) ? 0 : old_levels[i];
    levels[i] = next_level(conds.find(i+1)->second, old_level, accept_levels[i], finals_lists[i]);
  }
  
  return levels;
}

void make_RAtrans(const RAstate *s) {
  std::map<DRAstate*, DRAtrans>::iterator t_i;
  std::map<GenCondMap_t, bdd>::iterator c_i;
  
  for (t_i=s->d_state->trans->begin(); t_i!=s->d_state->trans->end(); t_i++) {
    for (c_i=t_i->second.conds_to_labels.begin(); c_i!=t_i->second.conds_to_labels.end(); c_i++) {
      std::vector<int> levels = next_levels(c_i->first, s->levels);
      RAstate* prod_to = new RAstate(t_i->first->id, levels, t_i->first);
      
      RAstate* to = find_rastate(prod_to);
      s->insert_transition(c_i->second, to);
    }
  }
}

/********************************************************************\
|*              Simplification of the Rabin automaton               *|
\********************************************************************/

bool ra_acceptance_match(RAstate *s1, RAstate *s2) {
  int i;

  for (i = 0; i < levels_num; i++) {
    // Skip removed conditions
    if (tl_dra_opt && isRemoved[i])
      continue;

    if(((s1->levels[i] == accept_levels[i]) != (s2->levels[i] == accept_levels[i])) ||
       ((s1->levels[i] == -1) != (s2->levels[i] == -1)))
      return false;
  }

  return true;  
}

bool all_ratrans_match(RAstate *s1, RAstate *s2) {
  std::map<RAstate*, RAtrans>::iterator m_1, m_2;

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

void decrement_incoming(std::map<RAstate*, RAtrans> *trans) {
  std::map<RAstate*, RAtrans>::iterator t;
  for(t = trans->begin(); t != trans->end(); t++)
      t->first->incoming--;
}

void remove_rastate(RAstate *s, RAstate *sub) {
  std::set<RAstate*, RAstateComp>::iterator s_i;

  decrement_incoming(s->trans);
  delete s->trans;
  s->trans = (std::map<RAstate*, RAtrans>*) 0;
  
  s->sub = sub;
  for (s_i = raRemoved.begin(); s_i != raRemoved.end(); s_i++)
    if ((*s_i)->sub == s)
      (*s_i)->sub = sub;
  raRemoved.insert(s);
}

void retarget_all_ratrans() {
  std::set<RAstate*, RAstateComp>::iterator s_i;
  std::map<RAstate*, RAtrans>::iterator t_i, t_temp;
  std::map<RAstate*, RAtrans>* trans;
  std::map<GenCondMap_t, bdd>::iterator m_i;

  if (raRemoved.size() == 0)
    return;
  
  if (!ra_init->trans)
    ra_init = ra_init->sub; // ra_init has been removed -> replace it
    
  for (s_i = rastates.begin(); s_i != rastates.end(); s_i++) {
    trans = (*s_i)->trans;
    for (t_i = trans->begin(); t_i != trans->end(); ) {
      if (!t_i->first->trans && // t->to has been removed
           t_i->first->sub) { // t->to has substitute -> retarget transition there
        RAtrans t = t_i->second;
        t.to = t_i->first->sub;
        t_temp = t_i;
        t_i++;
        if (trans->find(t.to) == trans->end()) {
          // transition to t.to state does not exist -> create a new one
          trans->insert(std::make_pair(t.to, t));
          t.to->incoming++;
        } else {
          // transition to t.to state does exist -> update it
          RAtrans *t1 = &(trans->find(t.to)->second);
          bdd *l = &(t1->label);
          if (*l == bdd_false()) {
            *l = t.label;
          } else {
            *l |= t.label;
          }
        }
        // erase the old transition (the one going to a removed state)
        trans->erase(t_temp);
      } else {
        t_i++;
      }
    }
  }
  
  for (s_i = raRemoved.begin(); s_i != raRemoved.end(); s_i++) {
    delete *s_i; 
  }
  raRemoved.clear();
}

void simplify_rastates() {
  bool removed = false;
  std::set<RAstate*, RAstateComp>::iterator s_i, s_j, s_temp;

  do {
    for(s_i = rastates.begin(); s_i != rastates.end(); s_i++) {
//      if(s_i->trans->empty()) { // s_i has no transitions
//        remove_rastate(s_i, (DRAstate *)0);
//        s_temp = s_i;
//        s_i++;
//        rastates.erase(s_temp);
//        continue;
//      }

      s_j = s_i;
      for (s_j++; s_j != rastates.end();) {
        if(ra_acceptance_match(*s_i, *s_j) &&
           all_ratrans_match(*s_i, *s_j)) { // s_i and s_j are equivalent
          remove_rastate(*s_j, *s_i);
          s_temp = s_j;
          s_j++;
          rastates.erase(s_temp);
        } else {
          s_j++;
        }
      }
    }

    if (raRemoved.size() > 0) {
      removed = true;
      retarget_all_ratrans();
    } else {
      removed = false;
    }
  } while (removed);
}

void remove_redundant_ra_init() {
  if (ra_init->incoming == 0) {
    std::list<RAstate*>::iterator i;
    for (i=init_copies.begin(); i!=init_copies.end(); i++) {
      if ((*i)->incoming != 0) {
        // Delete old initial state
        rastates.erase(ra_init);
        decrement_incoming(ra_init->trans);
        delete ra_init;
        // Set new initial state
        ra_init = *i;
        return;
      }
    }
  }
}

/********************************************************************\
|*                  Display of the Rabin automaton                  *|
\********************************************************************/

/*
std::ostream& dra::operator<<(std::ostream &out, const RAstate &r) {
  int i;
  bool start = true;

  std::cout << r.id << ": [" << r.d_state->id << ":<";
  for (i = 0; i < levels_num; i++) {
    // Skip removed conditions
    if (tl_dra_opt && isRemoved[i])
      continue;
    if (!start)
      out << ",";
    if(r.levels[i] == accept_levels[i])
      out << "*";
    out << r.levels[i];
    start = false;
  }
  out << ">]";
  return out;
} */

std::ostream& dra::operator<<(std::ostream &out, const RAstate &r) {
  int i;

  if (tl_verbose == 2 || tl_hoaf > 2) {
      bool first_level = true;
      bool first_acc = true;
      int level_counter = 0;

      out << "\"[" << state2Int[r.d_state] << ":<";
      for (i = 0; i < levels_num; i++) {
          // Skip removed conditions
          if (tl_dra_opt && isRemoved[i])
              continue;
          if (!first_level) {out << ",";}
          if (first_level)  {first_level = false;}
          out << r.levels[i];
      }
      out << ">]\" ";

      //Accepting
      for (i = 0; i < levels_num; i++) {
          // Skip removed conditions
          if (tl_dra_opt && isRemoved[i])
              continue;
          if(r.levels[i] == -1) {
              if (!first_acc) {out << " ";}
              if (first_acc) {out << "{"; first_acc = false;}
              out << 2*level_counter;
          }
          if(r.levels[i] == accept_levels[i]) {
              if (!first_acc) {out << " ";}
              if (first_acc) {out << "{"; first_acc = false;}
              out << 2*level_counter+1;
          }
          ++level_counter;
      }
      if (!first_acc)
          out << "}";
  } else {
      int i;
      bool start = true;

      std::cout << r.id << ": [" << r.d_state->id << ":<";
      for (i = 0; i < levels_num; i++) {
        // Skip removed conditions
        if (tl_dra_opt && isRemoved[i])
          continue;
        if (!start)
          out << ",";
        if(r.levels[i] == accept_levels[i])
          out << "*";
        out << r.levels[i];
        start = false;
      }
      out << ">]";
  }
  return out;
}

/*
std::ostream& dra::operator<<(std::ostream &out, const RAtrans &t) {
  where_os = &out;
  print_or = 0;

  if (t.label == bdd_true())
    out << "(1)";
  else
    bdd_allsat(t.label, allsatPrintHandler);
  out << " -> " << t.to->id << "\t";
  
  return out;
}
*/

std::ostream& dra::operator<<(std::ostream &out, const RAtrans &t) {
  where_os = &out;
  print_or = 0;

  if (tl_verbose == 2 || tl_hoaf > 2) {
    out << "[";
    if (t.label == bdd_true())
      out << "t";
    else
      bdd_allsat(t.label, allsatPrintHandler_hoaf);
    out << "] " << rastate2Int[t.to];
  } else {
    if (t.label == bdd_true())
      out << "(1)";
    else
      bdd_allsat(t.label, allsatPrintHandler);
    out << " -> " << t.to->id << "\t";
  }
  return out;
}

void print_dra_hoaf_header(int states,
                             std::map<RAstate*, int> rastate2Int,
                             const std::map<int, std::pair<int, int> >& Zindex_to_hoaf,
                             const std::string& ra_name = "DRA"
                             ) {
  std::cout << "HOA: v1";
  std::cout << "\ntool: \"ltl3dra\" \"" << VERSION_NUM << "\"";
  std::cout << "\nname: \"" << ra_name << " for " << uform << "\"";
  std::cout << "\nStates: " << states;
  if (states > 0) {
    std::cout << "\nStart: " << rastate2Int[ra_init];
    std::cout << "\nacc-name: Rabin " << Zindex_to_hoaf.size();
    std::cout << "\nAcceptance: " << 2*Zindex_to_hoaf.size() << " ";
    if (Zindex_to_hoaf.size()>0) {
      for(int i = 0; i < Zindex_to_hoaf.size();++i) {
        if (i > 0)
          std::cout << " | ";
        std::cout << "(Fin(" << 2*i << ")&Inf(" << 2*i + 1 << "))";
      }
    } else {
      std::cout << " f";
    }
    std::cout << "\nAP: " << predicates;
    for (int i = 0; i < predicates; ++i) {
      std::cout << " \"" << sym_table[i] << "\"";
    }
    std::cout << "\nproperties: deterministic trans-labels explicit-labels state-acc no-univ-branch";
  } else {
    std::cout << "\nacc-name: none";
    std::cout << "\nAcceptance: 0 f";
  }
}


void print_ra_hoaf(std::ostream &out, const std::string& name = "") {
  rastate2Int.clear();
  std::set<RAstate*, RAstateComp>::iterator s_i;
  std::map<RAstate*, RAtrans>::iterator t_i;
  // Create the mapping from DRAstates to their HOAF id.
  int state_count = 0;
  for(s_i=rastates.begin(); s_i!=rastates.end(); s_i++) {
    rastate2Int[*s_i] = state_count++;
  }
  if (name != "") {
    print_dra_hoaf_header(state_count,rastate2Int,Zindex_to_hoaf,name);
  } else {
    print_dra_hoaf_header(state_count,rastate2Int,Zindex_to_hoaf);
  }
  out << "\n--BODY--";
  
  for(s_i=rastates.begin(); s_i!=rastates.end(); s_i++) {
/*    out << "state " << (*s_i)->id << " : " << *(*s_i) << std::endl;*/
    out << "\nState: " << rastate2Int[*s_i] << " " << *(*s_i);
    for(t_i=(*s_i)->trans->begin(); t_i!=(*s_i)->trans->end(); t_i++) {
      out << "\n  " << t_i->second;
    }
  }
  out << "\n--END--" << std::endl;
}

void print_ra_old(std::ostream &out) {
  std::set<RAstate*, RAstateComp>::iterator s_i;
  std::map<RAstate*, RAtrans>::iterator t_i;

  out << "Init: " << *ra_init << std::endl;
  for(s_i=rastates.begin(); s_i!=rastates.end(); s_i++) {
/*    out << "state " << (*s_i)->id << " : " << *(*s_i) << std::endl;*/
    out << "state " << *(*s_i) << std::endl;
    for(t_i=(*s_i)->trans->begin(); t_i!=(*s_i)->trans->end(); t_i++) {
      out << "\t" << t_i->second << std::endl;
    }
  }
}


void new_state(int dstarid,RAstate* state) {
  dstarMap.insert(std::pair<int,RAstate*>(dstarid,state));
  id2dstar.insert(std::pair<int,int>(state->id,dstarid));
}

void print_ra_ltl2dstar(std::ostream &out) {
  std::set<RAstate*, RAstateComp>::iterator s_i;
  std::map<RAstate*, RAtrans>::iterator t_i;

  std::list<bdd>::reverse_iterator l_i;
  int id=0;
  int current_id=0;


  new_state(id++,ra_init);

  // Header
  out << "DRA v2 explicit" << std::endl;
  out << "Comment: \"Created by LTL3DRA v." << VERSION_NUM << "\"" << std::endl;
  out << "States: " << rastates.size() << std::endl;
  out << "Acceptance-Pairs: " << (Z_set.size()-removedConds) << std::endl;
  out << "Start: 0" << std::endl;
  out << "AP: " << sym_id;
  for (int i=0;i<sym_id;i++) out << " \"" << sym_table[i] << "\"";
  out << std::endl << "---" << std::endl;

  while (dstarMap[current_id]) {
      int skipped_Z = 0;
      out << "State: " << current_id << std::endl;
      out << "Acc-Sig: ";
      for (int l = 0; l < levels_num; l++) {
        // Skip removed conditions
        if (tl_dra_opt && isRemoved[l]) {
          skipped_Z++;
          continue;
        }
        if(dstarMap[current_id]->levels[l] == accept_levels[l])
          out << " +" << l-skipped_Z;
        if (dstarMap[current_id]->levels[l] == -1)
          out << " -" << l-skipped_Z;
      }
      out << std::endl;

      // Transitions
      for(l_i=det_constraints.rbegin(); l_i!=det_constraints.rend(); ++l_i) {
        // Search for appropriete transition that covers label l_i
        for(t_i=dstarMap[current_id]->trans->begin();t_i!=dstarMap[current_id]->trans->end();t_i++) {
          if ((*l_i >> t_i->second.label)==bdd_true()) {
              if (id2dstar.find(t_i->second.to->id) == id2dstar.end()) {
                 new_state(id++,t_i->second.to);
              }
            out << id2dstar[t_i->second.to->id] << std::endl;
            break;
          }
        }
      }
      current_id++;
  }

  /*// States and transitions
  for(s_i=rastates.begin(); s_i!=rastates.end(); s_i++) {
    out << "State: " << (*s_i)->id << std::endl;
    out << "Acc-Sig: ";
    for (int l = 0; l < levels_num; l++) {
      // Skip removed conditions
      if (tl_dra_opt && isRemoved[l])
        continue;
      if((*s_i)->levels[l] == accept_levels[l])
        out << " +" << l;
      if ((*s_i)->levels[l] == -1)
        out << " -" << l;
    }
    out << std::endl;

    // Transitions
    for(l_i=det_constraints.rbegin(); l_i!=det_constraints.rend(); ++l_i) {
      // Search for appropriete transition that covers label l_i
      for(t_i=(*s_i)->trans->begin();t_i!=(*s_i)->trans->end();t_i++) {
        if ((*l_i >> t_i->second.label)==bdd_true()) {
          out << t_i->second.to->id << std::endl;
          break;
        }
      }
    }
  }*/
}

void printGoalTrans(std::ostream &out) {
out << "\t\t<Transition tid=\"" << tid++ << "\">" << std::endl;
out << "\t\t\t<From>" << from << "</From>" << std::endl;
out << "\t\t\t<To>" << to << "</To>" << std::endl;
}


void goalPrintHandler(char* varset, int size)
{
  int print_and = 0;

  if (print_or) {
      *goal_output << "\t\t\t</Label>" << std::endl;
      *goal_output << "\t\t\t<Properties/>" << std::endl;
      *goal_output << "\t\t</Transition>" << std::endl;
      printGoalTrans(*goal_output);
      *goal_output << "\t\t<Label>" << std::endl;
  }
  //fprintf(tl_out, "(");
  for (int v=0; v<size; v++)
  {
    if (varset[v] < 0) continue;
    if (print_and) *goal_output << " ";
    if (varset[v] == 0)
      *goal_output << "~" << sym_table[v];
      //fprintf(tl_out, "~%s", sym_table[v]);
    else
      *goal_output << sym_table[v];
      //fprintf(tl_out, "%s", sym_table[v]);
    print_and = 1;
  }
  //fprintf(tl_out, ")");
  print_or = 1;
}

void print_ra_goal(std::ostream &out) {
  std::set<RAstate*, RAstateComp>::iterator s_i;
  std::map<RAstate*, RAtrans>::iterator t_i;
  std::vector<std::vector<int> > acc(levels_num),rej(levels_num);
  RAtrans tr;

  gout = &out;
  //where_os = &out;
  print_or = 0;

  // Print preface
  out << "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>" << std::endl;
  out << "<Structure label-on=\"Transition\" type=\"FiniteStateAutomaton\">" << std::endl;
  out << "\t<Name/>\n\t<Description/>" << std::endl << std::endl;

  // Print alphabet
  out << "\t<Alphabet type=\"Propositional\">" << std::endl;
  for (int i = 0; i < sym_id; i++) {
      out << "\t\t<Proposition>" << sym_table[i] << "</Proposition>" << std::endl;
  }
  out << "\t</Alphabet>" << std::endl << std::endl;

  // Print states
  out << "\t<StateSet>" << std::endl;
  for (s_i = rastates.begin(); s_i != rastates.end(); s_i++) {
    RAstate r = *(*s_i);
    out << "\t\t<State sid=\"" << r.id << "\">" << std::endl;
    //out << "\t\t\t<Description>" << *(*s_i) << "</Description>" << std::endl;
    out << "\t\t\t<Properties>" << std::endl;
    out << "\t\t\t\t<Entry name=\"Generalized state\">" << r.d_state->id << "</Entry>" << std::endl;
    out << "\t\t\t</Properties>" << std::endl;
    out << "\t\t</State>" << std::endl;

    // Store the state into right accepting sets
    for (int i = 0; i < levels_num; i++) {
        if (tl_dra_opt && isRemoved[i])
          continue;
        if(r.levels[i] == accept_levels[i])
          acc[i].push_back(r.id);
        if(r.levels[i] == -1)
          rej[i].push_back(r.id);
    }
  }
  out << "\t</StateSet>" << std::endl << std::endl;

  // Print initial state
  out << "\t<InitialStateSet>" << std::endl;
  out << "\t\t<StateID>" << ra_init->id << "</StateID>" << std::endl;
  out << "\t</InitialStateSet>" << std::endl << std::endl;

  // Print transitions
  out << "\t<TransitionSet>" << std::endl;
  for (s_i = rastates.begin(); s_i != rastates.end(); s_i++) {
    for(t_i=(*s_i)->trans->begin(); t_i!=(*s_i)->trans->end(); t_i++) {
      tr = t_i->second;
      from = (*s_i)->id;
      to = tr.to->id;
      printGoalTrans(out);

      //Print label
      out << "\t\t\t<Label>";
      print_or = 0;
      if (tr.label == bdd_true())
        out << "True";
      else
          bdd_allsat(tr.label, goalPrintHandler);
      out << "</Label>" << std::endl;

      out << "\t\t\t<Properties/>" << std::endl;
      out << "\t\t</Transition>" << std::endl;
    }
  }
  out << "\t</TransitionSet>" << std::endl << std::endl;

  // Print acceptance condition
  out << "\t<Acc type=\"Rabin\">" << std::endl;
  for (int i = 0; i < levels_num; i++) {
    if (tl_dra_opt && isRemoved[i])
      continue;
    out << "\t\t<AccPair>" << std::endl;
    out << "\t\t\t<F>" << std::endl;
    for (int j = 0; j < acc[i].size();j++) {
      out << "\t\t\t\t<StateID>" << acc[i][j] << "</StateID>" << std::endl;
    }
    out << "\t\t\t</F>" << std::endl;
    out << "\t\t\t<E>" << std::endl;
    for (int j = 0; j < rej[i].size();j++) {
      out << "\t\t\t\t<StateID>" << rej[i][j] << "</StateID>" << std::endl;
    }
    out << "\t\t\t</E>" << std::endl;
    out << "\t\t</AccPair>" << std::endl;
  }
  out << "\t</Acc>" << std::endl << std::endl;

  // Print enclosure
  out << "\t<Properties/>" << std::endl;
  out << "</Structure>" << std::endl;
}

/*******************************************************************\
|*                  Computing statistics                           *|
\*******************************************************************/

/* One edge can represent multiple transitions with the same target
   under different labels                                        */
int get_dra_edges() {
    int count = 0;
    std::set<DRAstate*, DRAstateComp>::iterator s_i;
    // Iterates over states
    for (s_i = drastates.begin();s_i != drastates.end();s_i++) {
      DRAstate s = *(*s_i);
      std::map<DRAstate*, DRAtrans>::iterator medge;
      // Iterates over target states
      // Each medge can represent multiple edges with different AC
      for (medge = (s.trans)->begin();medge != (s.trans)->end();medge++) {
          count += medge->second.conds_to_labels.size();
      }
    }
    return count;
//  int count = 0;
//  std::set<DRAstate*, DRAstateComp>::iterator s_i;
//  for (s_i = drastates.begin();s_i != drastates.end();s_i++) {
//      count += (*(s_i))->trans->second.conds_to_labels.size();
//  }
//  return count;
}
int get_dra_trans() {
    int count = 0;
    std::set<DRAstate*, DRAstateComp>::iterator s_i;
    for (s_i = drastates.begin();s_i != drastates.end();s_i++) {
      DRAstate s = *(*s_i);
      std::map<DRAstate*, DRAtrans>::iterator edge;
      // Iterates over edges and counts transitions
      for (edge = (s.trans)->begin();edge != (s.trans)->end();edge++) {
         std::map<GenCondMap_t, bdd> cond = edge->second.conds_to_labels;
         std::map<GenCondMap_t, bdd>::iterator c;
         // Iterates over edges and counts respective transitions
         for (c = cond.begin();c != cond.end();c++) {
             count+= bdd_satcount(c->second);
         }
      }
    }
    return count;
}
int get_ra_edges() {
    int count = 0;
    std::set<RAstate*, RAstateComp>::iterator s_i;
    for (s_i = rastates.begin();s_i != rastates.end();s_i++) {
      count += (*(s_i))->trans->size();
    }
    return count;
}
int get_ra_trans() {
    int count = 0;
    std::set<RAstate*, RAstateComp>::iterator s_i;
    for (s_i = rastates.begin();s_i != rastates.end();s_i++) {
      std::map<RAstate *, RAtrans>::iterator e_i;
      for(e_i = (*s_i)->trans->begin();e_i != (*s_i)->trans->end();e_i++) {
          count += bdd_satcount(e_i->second.label);
      }
    }
    return count;
}

int get_acc_size() {
    int size = 0;
    std::set<cset>::iterator s_i;
    cset temp;
    for (s_i = Z_set.begin(); s_i != Z_set.end(); s_i++) {
      int i = Z_setToInt[*s_i]-1;
      if (tl_dra_opt) {if (isRemoved[i]) continue;}
      size += accept_levels[i];
    }
    return size;
}

/********************************************************************\
|*                       Main method                                *|
\********************************************************************/

void mk_ra() 
{/* generates a Rabin automaton from the generalized Rabin automaton */
  levels_num = Z_set.size();
  accept_levels.resize(levels_num);
  finals_lists.resize(levels_num);
  {
    std::set<cset>::iterator s_i;
    cset temp;
    for (s_i = Z_set.begin(); s_i != Z_set.end(); s_i++) {
      temp.intersect_sets(*s_i, final_set);
      int i = Z_setToInt[*s_i]-1;
      if (tl_dra_opt) {
        // remove removed I_k sets
        temp.substract(removedI_sets[i]);
      }
      finals_lists[i] = temp.to_list();
      accept_levels[i] = finals_lists[i][0]-1;
    }
  }

  ra_init = new RAstate(RAstate_id++, levels_num, dra_init);
  rastates.insert(ra_init);
  raqueue.push(ra_init);

  while(!raqueue.empty()) { /* solves all states in the stack until it is empty */
    const RAstate* ra = raqueue.front();
    raqueue.pop();

    make_RAtrans(ra);
  }
  
  remove_redundant_ra_init();
  
  if (tl_verbose && tl_simp_diff && !tl_dra_stats) {
    if (tl_verbose == 1) {
        std::cout << std::endl << std::endl << "DRA before simplification" << std::endl;
        print_ra_old(std::cout);
        std::cout << std::endl;
    } else {
    print_ra_hoaf(std::cout, "DRA before simplification");
    }
  }
  
  if(tl_simp_diff) {
    simplify_rastates();
    remove_redundant_ra_init();
  }

//  if (!tl_dra_stats) {
//  fprintf(tl_out, "\nDRA in internal format\n");
  if (tl_verbose == 1) {
    std::cout << "DRA after simplification" << std::endl;
    print_ra_old(std::cout);
    std::cout << std::endl << std::endl << "DRA in ltl2dstar format" << std::endl << std::endl;
  }

  if (tl_spot_out == 3)
    print_ra_old(std::cout);

  if (tl_verbose == 2 || tl_hoaf == 3) {
    print_ra_hoaf(std::cout);
  }

  if (tl_dra_ltl2dstar)
    print_ra_ltl2dstar(std::cout);
//  }

  if(tl_dra_goal) {
    print_ra_goal(*goal_output);
    goal_output->flush();
    automaton->flush();
    automaton->close();
//  std::cout << rastates.size() << "(" << (Z_set.size()-removedConds) << ") & " << drastates.size() << " \\\\ \\hline " << std::endl;
  }

//  if(!tl_dra_stats && !tl_verbose) {
//  std::cout << std::endl << "-----------------------------------" << std::endl << std::endl;
//  std::cout << "Acceptance-Pairs: " << (Z_set.size()-removedConds) << std::endl;
//  std::cout << "States: " << rastates.size() << std::endl;
//  std::cout << "States of generalized automaton: " << drastates.size() << std::endl;
//  }

  if(tl_dra_stats || tl_verbose) {
    if (tl_verbose)
      std::cout << std::endl << "-----------------------------------\n";
    std::cout << "\nStates of TGDRA: " << drastates.size();
    std::cout << "\nEdges of TGDRA: " << get_dra_edges();
    std::cout << "\nTransitions of TGDRA: " << get_dra_trans();
    std::cout << "\nAcceptance-Pairs: " << (Z_set.size()-removedConds);
    std::cout << "\nInfinite-Sets: " << get_acc_size();
    std::cout << "\nStates of DRA: " << rastates.size();
    std::cout << "\nEdges of DRA: " << get_ra_edges();
    std::cout << "\nTransitions of DRA: " << get_ra_trans() << std::endl;
  }

  for (int i = 0; i < levels_num; i++) {
    tfree(finals_lists[i]);
  }
}
