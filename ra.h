/***** ltl3dra : ra.h *****/

/* Copyright (c) 2013  Tomas Babiak and Frantisek Blahoudek               */
/*                                                                        */
/* This program is free software; you can redistribute it and/or modify   */
/* it under the terms of the GNU General Public License as published by   */
/* the Free Software Foundation; either version 3 of the License, or      */
/* (at your option) any later version.                                    */
/*                                                                        */
/* This program is distributed in the hope that it will be useful,        */
/* but WITHOUT ANY WARRANTY; without even the implied warranty of         */
/* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          */
/* GNU General Public License for more details.                           */
/*                                                                        */
/* GNU GPL is included in this distribution, in a file called 'LICENSE'.  */
/* If not, see <https://www.gnu.org/licenses/>.                           */


#include "dra.h"

#include <map>
#include <set>
#include <vector>

namespace dra {

class RAtrans;

class RAstate {
  private:
    
  public:  
    int id;
    int incoming;
    std::vector<int> levels;
    DRAstate* d_state;
    RAstate* sub;
    
    std::map<RAstate*, RAtrans>* trans;
    
    RAstate(int id, int size, DRAstate* ds) { this->id = id; trans = new std::map<RAstate*, RAtrans>();
                                              levels = std::vector<int>(size, 0); d_state = ds; this->incoming = 0; }
    RAstate(int id, std::vector<int>& l, DRAstate* ds) { this->id = id; trans = new std::map<RAstate*, RAtrans>();
                                                    levels = l; d_state = ds; this->incoming = 0;}
    RAstate(const RAstate &r) { this->id = r.id; this->levels = r.levels; this->d_state = r.d_state;
                                if (r.trans) this->trans = new std::map<RAstate*, RAtrans>(*r.trans);
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

// Declare all stream operators in dra namespace.
std::ostream& operator<<(std::ostream &out, const RAstate &r);
std::ostream& operator<<(std::ostream &out, const RAtrans &t);

}
