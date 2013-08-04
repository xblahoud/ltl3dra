#include "dra.h"

#include <map>
#include <set>
#include <vector>

using namespace std;
namespace dra {

class RAtrans;

class RAstate {
  private:
    
  public:  
    int id;
    int incoming;
    vector<int> levels;
    DRAstate* d_state;
    RAstate* sub;
    
    std::map<RAstate*, RAtrans>* trans;
    
    RAstate(int id, int size, DRAstate* ds) { this->id = id; trans = new map<RAstate*, RAtrans>();
                                              levels = vector<int>(size, 0); d_state = ds; this->incoming = 0; }
    RAstate(int id, vector<int>& l, DRAstate* ds) { this->id = id; trans = new map<RAstate*, RAtrans>();
                                                    levels = l; d_state = ds; this->incoming = 0;}
    RAstate(const RAstate &r) { this->id = r.id; this->levels = r.levels; this->d_state = r.d_state;
                                if (r.trans) this->trans = new map<RAstate*, RAtrans>(*r.trans);
                                this->incoming = r.incoming;}
    ~RAstate() { if (trans) delete trans; }
    
    //RAstate& operator=(const RAstate &r);
    // It is expected that d_state and r.d_state are not null therefore the checks are omitted
    bool operator<(const RAstate &r) const { return (d_state->id < r.d_state->id) || (d_state->id == r.d_state->id && levels < r.levels); }
    bool operator==(const RAstate &r) const { return (d_state->id == r.d_state->id && levels == r.levels); }
    bool operator!=(const RAstate &r) const { return (d_state->id != r.d_state->id || levels != r.levels); }
    
    friend std::ostream &operator<<(std::ostream &out, const RAstate &r);

    void insert_transition(bdd label, RAstate* to) const;
};

struct RAstateComp {
  bool operator() (const RAstate* lhs, const RAstate* rhs) const
  {return *lhs<*rhs;}
};

extern int RAtrans_id;

class RAtrans {
  public:
    int id;
  
    RAstate* to;
    bdd label;
    
    RAtrans() { id = RAtrans_id++; label = bdd_true(); }
    RAtrans(bdd l, RAstate* t) { to = t; id = RAtrans_id++; label = l; }
    RAtrans(const RAtrans &t) { this->to = t.to; id = t.id; label = t.label; }
    
    bool operator<(const RAtrans &t) const { return (label.id() < t.label.id()) || (label == t.label && to < t.to); }
    bool operator==(const RAtrans &t) const { return label == t.label && to == t.to; }
    bool operator!=(const RAtrans &t) const { return label != t.label || to != t.to; }

    friend std::ostream& operator<<(std::ostream &out, const RAtrans &t);
    
    void insert_label(bdd l) { label |= l; }
};

}
