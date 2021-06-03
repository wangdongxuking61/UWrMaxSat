/**************************************************************************************[MsSolver.h ]
  Copyright (c) 2018-2019, Marek Piotrów

  Based on PbSolver.h ( Copyright (c) 2005-2010, Niklas Een, Niklas Sorensson)

  Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
  associated documentation files (the "Software"), to deal in the Software without restriction,
  including without limitation the rights to use, copy, modify, merge, publish, distribute,
  sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all copies or
  substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
  NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
  DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
  OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
  **************************************************************************************************/

#ifndef MsSolver_h
#define MsSolver_h

#include "PbSolver.h"
#include "algsatlike.h"
#include <vector>
#include <algorithm>
#include <scip/scip.h>
#include <scip/scipdefplugins.h>

Int evalGoal(const vec<Pair<weight_t, Minisat::vec<Lit>* > >& soft_cls, vec<bool>& model, Minisat::vec<Lit>& soft_unsat);

static inline int hleft (int i)  { return i * 2; }
static inline int hright(int i)  { return i * 2 + 1; }
static inline int hparent(int i) { return i / 2; }

class IntLitQueue {
  private:
    vec<Pair<Int, Lit> > heap;
    std::map<Lit, int> core_size;

    bool cmp(int x, int y) { 
        if(weighted_instance)
            return heap[x].fst > heap[y].fst;
        else
        {
            if(heap[x].fst != heap[y].fst)  return heap[x].fst > heap[y].fst;
            else                            return core_size[heap[x].snd] < core_size[heap[y].snd];
        }
    }

  public:
    bool weighted_instance = false;
    
    IntLitQueue() { heap.push(Pair_new(1, lit_Undef)); }

    bool empty() { return heap.size() <= 1; }

    const vec<Pair<Int, Lit> >& getHeap() const { return heap; }

    void clear() { heap.shrink(heap.size() - 1); }

    const Pair<Int, Lit>& top() { return heap[1]; }

    void push(Pair<Int, Lit> p, int core_size = 0) {
        this->core_size[p.snd] = core_size;
        heap.push();
        int i = heap.size() - 1;
        heap[0] = std::move(p);
        while (hparent(i) != 0 && cmp(0, hparent(i))) { // percolate up
            heap[i] = std::move(heap[hparent(i)]);
            i       = hparent(i);
        }
        heap[i] = std::move(heap[0]);
    }

    void pop(void) {
        heap[1] = std::move(heap.last());
        heap.pop();
        if (heap.size() > 1) { // percolate down
            int i = 1;
            heap[0] = std::move(heap[1]);
            while (hleft(i) < heap.size()){
                int child = hright(i) < heap.size() && cmp(hright(i), hleft(i)) ? hright(i) : hleft(i);
                if (!cmp(child, 0)) break;
                heap[i] = std::move(heap[child]);
                i       = child;
            }
            heap[i] = std::move(heap[0]);
        }
    }

} ;

class MsSolver : public PbSolver {
  public:
    MsSolver(bool use_preprocessing = false) : 
          PbSolver(use_preprocessing)
        , harden_goalval(0)
        , fixed_goalval(0)
        , goal_gcd(1)      {}
    /***------ params for satlike ----***/
    bool satlike_is_use =true;
    bool use_hard_clause_value_init =true;
    bool use_add_constr = true;
    Minisat::vec<Lit> sat_clause_first;
    Minisat::vec<Lit> unsat_clause_first;
    Minisat::vec<Lit> unsat_clause_second;
    vec<Int> unsat_clause_second_Cs;
    std::vector<std::vector<Lit>> am1_cls;
    Satlike satlike;
    /***------ params for satlike ----***/
    std::vector<std::vector<Lit>>constr_scip;               // saving the constraint from satlike to scip
    Int goalvalue_satlike = INT_MAX;
    std::string model_value;
    Int                 harden_goalval,  //  Harden goalval used in the MaxSAT preprocessing 
                        fixed_goalval;   // The sum of weights of soft clauses that must be false
    vec<Pair<weight_t, Minisat::vec<Lit>* > > orig_soft_cls; // Soft clauses before preprocessing by MaxPre; empty if MaxPre is not used
    vec<Pair<weight_t, Minisat::vec<Lit>* > > soft_cls; // Relaxed non-unit soft clauses with weights; a relaxing var is the last one in a vector. 
    weight_t            goal_gcd; // gcd of soft_cls weights
    int                 top_for_strat, top_for_hard; // Top indices to soft_cls for stratification and hardening operations.
    Map<Lit, Int>       harden_lits;    // The weights of literals included into "At most 1" clauses (MaxSAT preprocessing of soft clauese).
    vec<Pair<Lit,Int> > am1_rels;       // The weights of relaxing vars in "At most 1" clauses

    void    storeSoftClause(const vec<Lit>& ps, weight_t weight) {
                Minisat::vec<Lit> *ps_copy = new Minisat::vec<Lit>; 
                for (int i = 0; i < ps.size(); i++) ps_copy->push(ps[i]); 
                soft_cls.push(Pair_new(weight, ps_copy)); }

    void    harden_soft_cls(Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs);
    void    optimize_last_constraint(vec<Linear*>& constrs, Minisat::vec<Lit>& assump_ps, Minisat::vec<Lit>& new_assump);
    SCIP_RETCODE scip_solve(const Minisat::vec<Lit> &assump_ps, const vec<Int> &assump_Cs, const IntLitQueue &delayed_assump, bool weighted_instance, bool &found_opt);
    void    maxsat_solve(solve_Command cmd = sc_Minimize); 
    void    preprocess_soft_cls(Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs, const Lit max_assump, const Int& max_assump_Cs, 
                                           IntLitQueue& delayed_assump, Int& delayed_assump_sum);
    void satlike_solve(vec<bool> &model_satlike);
    void add_benefit_constraint(vec<Pair<Lit,int> > &psCs,vec<bool> &model);
} ;

#endif
