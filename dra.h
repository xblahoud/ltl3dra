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
    std::set<cset> sets;
  
    int id;
    int incoming;
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
  private:
  
    // auxiliary functions
    GenCond allowed_for_Z(int i, const DRAstate* from, bdd label);
    GenCondMap_t evaluate_acc_cond(const DRAstate* from, bdd label);

  public:
    int id;
  
    DRAstate* to;
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
