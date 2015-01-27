#include "ltl3dra.h"

#include <map>
#include <set>
#include <list>
#include <vector>

using namespace std;
namespace dra {

GState *find_gstate(cset *set, GState *s);
void make_gtrans(GState *s);

class DRAtrans;

class DRAstate {
  private:
    
    
  public:
    std::set<cset> sets; // The set of configurations
  
    int id;
    int incoming; // The number of incoming transitions(edges)
    DRAstate* sub; // substitute
    
    std::map<DRAstate*, DRAtrans>* trans;
    
    DRAstate() { this->id = 0; trans = new map<DRAstate*, DRAtrans>(); this->incoming = 0; sub = NULL; }
    DRAstate(int id) { this->id = id; trans = new map<DRAstate*, DRAtrans>(); this->incoming = 0; sub = NULL; }
    DRAstate(int id, cset& s) { this->id = id; this->sets.insert(s); trans = new map<DRAstate*, DRAtrans>();
                                this->incoming = 0; sub = NULL; }
    DRAstate(const DRAstate &s) { this->id = s.id; this->sets = s.sets;
                                  if (s.trans) this->trans = new map<DRAstate*, DRAtrans>(*s.trans);
                                  this->incoming = s.incoming; this->sub = s.sub; }
    ~DRAstate() { if (trans) delete trans; }
    
    //DRAstate& operator=(const DRAstate &r);
    bool operator<(const DRAstate &r) const { return (sets < r.sets); }
    bool operator==(const DRAstate &r) const { return (sets == r.sets); }
    bool operator!=(const DRAstate &r) const { return (sets != r.sets); }
    
    friend std::ostream &operator<<(std::ostream &out, const DRAstate &r);

    void insert(cset &c);
    void clear() { sets.clear(); }
    void insert_transition(bdd label, DRAstate* to) const;
    
//    std::set<cset>& get_sets() { return sets; }
//    void replace_sets(std::set<cset> &s) { sets = s; }
};

struct DRAstateComp {
  bool operator() (const DRAstate* lhs, const DRAstate* rhs) const
  {return *lhs<*rhs;}
};

class GenCond {
    // A GenCond object serves to store information about one pair of a TGDRA acc. condition for one transition.
    // A gen. Rabin pair (F,{I_1,I_2,...,I_n}) is satisfied, if a run visits F only finitely many times and each
    // of I_i infinitely many times. In a GenCond object we store information wheter the according transition is
    // member of the F-set (the bool allowed), and whether it is a member of the I_i sets (the bool vector f_accepting)
  public:
    bool allowed;
    vector<bool> f_accepting;
    
    GenCond(int size) { f_accepting = vector<bool>(size, false); }
    GenCond(const GenCond &c) { allowed = c.allowed; f_accepting = c.f_accepting; }
    
    bool operator<(const GenCond &c) const { return ((allowed < c.allowed) || (allowed == c.allowed && f_accepting < c.f_accepting)); }
    bool operator==(const GenCond &c) const { return (allowed == c.allowed && f_accepting == c.f_accepting); }
    bool operator!=(const GenCond &c) const { return (allowed != c.allowed || f_accepting != c.f_accepting); }
    
    friend std::ostream &operator<<(std::ostream &out, const GenCond &t);
    void print(std::ostream &out, int Z_i) const;
};

typedef map<int, GenCond> GenCondMap_t;

extern int DRAtrans_id;

class DRAtrans {
    // A DRAtrans is an adge in the TGDRA automaton. The edge can be divided into transitions.
    // More transitions can be in the same accepting sets, they are than merged.
    // A single-letter labelled transition is identified by trans.id;tgdra_acc;label
  private:
  
    // auxiliary functions
    GenCond allowed_for_Z(int i, const DRAstate* from, bdd label);
    GenCondMap_t evaluate_acc_cond(const DRAstate* from, bdd label);

  public:
    int id;
  
    DRAstate* to;
    // Maps conditions to labels with that condition
    map<GenCondMap_t, bdd> conds_to_labels;
    
    DRAtrans(bdd l, const DRAstate* f, DRAstate* t) { to = t; id = DRAtrans_id++; insert_label(f, l); }
    DRAtrans(const DRAtrans &t) { this->to = t.to; id = t.id; conds_to_labels = t.conds_to_labels; }
    
//    bool operator<(const DRAtrans &t) const { return (to < t.to) || (to == t.to && conds_to_labels < t.conds_to_labels); }
    bool operator==(const DRAtrans &t) const { return to == t.to && conds_to_labels == t.conds_to_labels; }
    bool operator!=(const DRAtrans &t) const { return to != t.to || conds_to_labels != t.conds_to_labels; }

    friend std::ostream& operator<<(std::ostream &out, const DRAtrans &t);
    
    void insert_label(const DRAstate* from, bdd l);
    
    void remove_redundant_acc_conds(const list<int>& toBeRemoved);
};

}
