/**************************************************************************************[MsSolver.cc]
  Copyright (c) 2018-2019, Marek Piotrów

  Based on PbSolver.cc ( Copyright (c) 2005-2010, Niklas Een, Niklas Sorensson)

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

#include <unistd.h>
#include <signal.h>
#include <algorithm>
#include "System.h"
#include "Sort.h"
#include "Debug.h"

template<typename int_type>
static int_type gcd(int_type small, int_type big) {
    if (small < 0) small = -small;
    if (big < 0) big = -big;
    return (small == 0) ? big: gcd(big % small, small); }

template<typename T>
static int bin_search(const Minisat::vec<T>& seq, const T& elem)
{
    int fst = 0, cnt = seq.size();
    while (cnt > 0) {
        int step = cnt / 2, mid = fst + step;
        if (seq[mid] < elem) fst = mid + 1, cnt -= step + 1; 
        else cnt = step;
    }
    return (fst < seq.size() && seq[fst] == elem ? fst : -1);
}
        
template<typename T>
static int bin_search(const vec<T>& seq, const T& elem)
{
    int fst = 0, cnt = seq.size();
    while (cnt > 0) {
        int step = cnt / 2, mid = fst + step;
        if (seq[mid] < elem) fst = mid + 1, cnt -= step + 1; 
        else cnt = step;
    }
    return (fst < seq.size() && seq[fst] == elem ? fst : -1);
}
        
static MsSolver *pb_solver;
static
void SIGINT_interrupt(int signum) { 
    pb_solver->sat_solver.interrupt(); pb_solver->asynch_interrupt=true; 
#ifdef SIGXCPU    
    pb_solver->cpu_interrupt = (signum == SIGXCPU);
#else
    (void) signum;
    pb_solver->cpu_interrupt = false;
#endif
}

extern int verbosity;

static void clear_assumptions(Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs)
{
    int removed, j = 0;
    for (int i = 0; i < assump_ps.size(); i++) {
        if (assump_Cs[i] < 0) continue;
        if (j < i) assump_ps[j] = assump_ps[i], assump_Cs[j] = assump_Cs[i];
        j++;
    }
    if ((removed = assump_ps.size() - j) > 0)
        assump_ps.shrink(removed), assump_Cs.shrink(removed);
}

static
bool satisfied_soft_cls(Minisat::vec<Lit> *cls, vec<bool>& model)
{
    assert(cls != NULL);
    for (int i = cls->size() - 2; i >= 0; i--)
        if ((( sign((*cls)[i]) && !model[var((*cls)[i])]) 
          || (!sign((*cls)[i]) &&  model[var((*cls)[i])])))
            return true;
    return false;
}


Int evalGoal(const vec<Pair<weight_t, Minisat::vec<Lit>* > >& soft_cls, vec<bool>& model, 
        Minisat::vec<Lit>&soft_unsat)
{
    Int sum = 0;
    bool sat = false;
    soft_unsat.clear();
    for (int i = 0; i < soft_cls.size(); i++) {
        Lit p = soft_cls[i].snd->last(); if (soft_cls[i].snd->size() == 1) p = ~p;
        assert(var(p) < model.size());
        if ((( sign(p) && !model[var(p)]) || (!sign(p) &&  model[var(p)])) 
            && !(sat = satisfied_soft_cls(soft_cls[i].snd, model))) {
            if (opt_output_top > 0) soft_unsat.push(~p);
            sum += soft_cls[i].fst;
        } else if (opt_output_top > 0) {
            soft_unsat.push(p);
        }
        if (sat) { sat = false; model[var(p)] = !model[var(p)]; }
    }
    return sum;
}

static
void core_minimization(SimpSolver &sat_solver, Minisat::vec<Lit> &mus, int budget = 1000)
{
    int last_size = sat_solver.conflict.size();

    sat_solver.setConfBudget(budget);
    int verb = sat_solver.verbosity; sat_solver.verbosity = 0;
    for (int i = 0; last_size > 1 && i < last_size; ) {
        Lit p = mus[i];
        for (int j = i+1; j < last_size; j++) mus[j-1] = mus[j];
        mus.pop();
        if (sat_solver.solveLimited(mus) != l_False) {
            mus.push();
            for (int j = last_size - 1; j > i; j--) mus[j] = mus[j-1];
            mus[i] = p; i++;
        } else last_size--;
    }
    sat_solver.budgetOff(); sat_solver.verbosity = verb;

    for (int i = mus.size() - 1; i >= 0; i--) mus[i] = ~mus[i];
}

/*static void core_trimming(SimpSolver &sat_solver, int max_size, int n)
{
    int last_size = sat_solver.conflict.size();
    Minisat::vec<Lit> assump(last_size);
    for (int i = n; i > 0 && last_size > max_size; i--) {
        assump.clear();
        for (int j = 0; j < last_size; j++) assump.push(~sat_solver.conflict[j]);
        sat_solver.solve(assump);
        if (sat_solver.conflict.size() >= last_size) return;
        last_size = sat_solver.conflict.size();
    }
}*/

static Int next_sum(Int bound, const vec<Int>& cs)
{ // find the smallest sum of a subset of cs that is greater that bound
    vec<Int> sum[2];
    Int x, next_min = Int_MAX;
    int oldv =0, newv = 1, lst = 0;

    sum[oldv].push(0); ++bound;
    for (int sz = 1, j = 0; j < cs.size(); j++, oldv = newv, newv = 1-oldv, lst = 0) {
        for (int i = 0; i < sz; i++)
            if ((x = sum[oldv][i] + cs[j]) < bound) {
                while (lst < sz && sum[oldv][lst] > x) sum[newv].push(sum[oldv][lst++]);
                if (lst == sz || sum[oldv][lst] < x) sum[newv].push(x);
            } else if (x < next_min) {
                if (x == bound) return x;
                next_min = x;
            }
        while (lst < sz) sum[newv].push(sum[oldv][lst++]);
        sz = sum[newv].size(); sum[oldv].clear();
    }
    return (next_min == Int_MAX ? bound - 1 : next_min);

}

/*static
Int evalPsCs(vec<Lit>& ps, vec<Int>&Cs, vec<bool>& model)
{
    Int sum = 0;
    assert(ps.size() == Cs.size());
    for (int i = 0; i < ps.size(); i++){
        if (( var(ps[i]) >= model.size())
        ||  ( sign(ps[i]) && model[var(ps[i])] == false)
        ||  (!sign(ps[i]) && model[var(ps[i])] == true )
        )
            sum += Cs[i];
    }
    return sum;
}

static
Int evalPsCs(vec<Lit>& ps, vec<Int>&Cs, Minisat::vec<lbool>& model)
{
    Int sum = 0;
    assert(ps.size() == Cs.size());
    for (int i = 0; i < ps.size(); i++){
        if (( sign(ps[i]) && model[var(ps[i])] == l_False)
        ||  (!sign(ps[i]) && model[var(ps[i])] == l_True )
        )
            sum += Cs[i];
    }
    return sum;
}*/

static void opt_stratification(vec<weight_t>& sorted_assump_Cs, vec<Pair<Int, bool> >& sum_sorted_soft_cls)
{
    assert(sorted_assump_Cs.size() == sum_sorted_soft_cls.size());

    int m = max(1, sum_sorted_soft_cls.size() - 10);
    if (m < 10) m = 1;
    for (int i = sum_sorted_soft_cls.size() - 1; i >= m; i--)
        if (sorted_assump_Cs[i] > sorted_assump_Cs[i-1] + 1 || 
                i < sum_sorted_soft_cls.size() - 1 && !sum_sorted_soft_cls[i + 1].snd) 
            sum_sorted_soft_cls[i].snd = true;
    if (m == 1) return;
    vec<Pair<weight_t, int> > gaps;
    for (int i = 0; i < m; i++) gaps.push(Pair_new(sorted_assump_Cs[i+1] - sorted_assump_Cs[i], i + 1));
    sort(gaps);
    for (int i = gaps.size() - 1, j = 0; j < 10; j++, i--) sum_sorted_soft_cls[gaps[i].snd].snd = true;
}

template <class T> struct LT {bool operator()(T x, T y) { return x.snd->last() < y.snd->last(); }};

static weight_t do_stratification(SimpSolver& S, vec<weight_t>& sorted_assump_Cs, vec<Pair<weight_t,
        Minisat::vec<Lit>* > >& soft_cls, int& top_for_strat, Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs)
{
    weight_t  max_assump_Cs;
    max_assump_Cs = sorted_assump_Cs.last(); sorted_assump_Cs.pop();
    if (sorted_assump_Cs.size() > 0 && sorted_assump_Cs.last() == max_assump_Cs - 1) 
        max_assump_Cs = sorted_assump_Cs.last(), sorted_assump_Cs.pop(); 
    int start = top_for_strat - 1;
    while (start >= 0 && soft_cls[start].fst >= max_assump_Cs) start--;
    start++;
    if (start < top_for_strat) {
        int sz = top_for_strat - start, to = 0, fr = sz;
        sort(&soft_cls[start], sz, LT<Pair<weight_t, Minisat::vec<Lit>*> >());
        assump_ps.growTo(assump_ps.size() + sz); assump_Cs.growTo(assump_Cs.size() + sz);
        for (int i = assump_ps.size() - 1; i >= sz; i--)
            assump_ps[i] = assump_ps[i-sz], assump_Cs[i] = assump_Cs[i-sz];
        for (int i = start; i < top_for_strat; i++) {
            Lit p = ~soft_cls[i].snd->last();
            if (soft_cls[i].snd->size() > 1) S.addClause(*soft_cls[i].snd); else p = ~p;
            while (fr < assump_ps.size() && assump_ps[fr] <= p)
                assump_ps[to] = assump_ps[fr], assump_Cs[to++] = assump_Cs[fr++];
            assump_ps[to] = p; assump_Cs[to++] = soft_cls[i].fst;
        }
        sort(&soft_cls[start], sz);
        top_for_strat = start;
    }
    return max_assump_Cs;
}

void MsSolver::harden_soft_cls(Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs)
{
    int cnt_unit = 0, cnt_assump = 0, sz = 0;
    Int Ibound = UB_goalvalue - LB_goalvalue, WMAX = Int(WEIGHT_MAX);
    weight_t       wbound = (Ibound >= WMAX ? WEIGHT_MAX : tolong(Ibound));
    weight_t ub_goalvalue = (UB_goalvalue >= WMAX ? WEIGHT_MAX : tolong(UB_goalvalue - fixed_goalval));
    for (int i = top_for_hard - 1; i >= 0 && soft_cls[i].fst > wbound; i--) { // hardening soft clauses with weights > the current goal interval length 
        if (soft_cls[i].fst > ub_goalvalue) sz++;
        Lit p = soft_cls[i].snd->last(); if (soft_cls[i].snd->size() > 1) p = ~p;
        int j = bin_search(assump_ps, p);
        if (j >= 0 && assump_Cs[j] > Ibound) {
            if (opt_minimization == 1) harden_lits.set(p, Int(soft_cls[i].fst));
            assump_Cs[j] = -assump_Cs[j]; // mark a corresponding assumption to be deleted
            cnt_assump++; cnt_unit++; sat_solver.addClause(p);
        } else if (soft_cls[i].fst > ub_goalvalue) { 
            if (opt_minimization == 1) harden_lits.set(p, Int(soft_cls[i].fst));
            cnt_unit++, sat_solver.addClause(p);
        }
    }
    if (opt_verbosity >= 2 && cnt_unit > 0) reportf("Hardened %d soft clauses\n", cnt_unit);
    if (sz > 0 ) top_for_hard -= sz;
    if (cnt_assump > 0) clear_assumptions(assump_ps, assump_Cs);
}

void MsSolver::optimize_last_constraint(vec<Linear*>& constrs, Minisat::vec<Lit>& assump_ps, Minisat::vec<Lit>& new_assump)
{
    Minisat::vec<Lit> assump;
    if (constrs.size() == 0) return ;
    int verb = sat_solver.verbosity; sat_solver.verbosity = 0;
    bool found = false;

    sat_solver.setConfBudget(1000);
    if (sat_solver.solveLimited(assump_ps) == l_False) {
        for (int i=0; i < sat_solver.conflict.size(); i++)
            if (assump_ps.last() == ~sat_solver.conflict[i]) { found = true; break;}
        if (found) {
            if (constrs.size() > 1) {
                constrs[0] = constrs.last();
                constrs.shrink(constrs.size() - 1);
            }
            while (found && (constrs[0]->lo > 1 || constrs[0]->hi < constrs[0]->size - 1)) {
                if (constrs[0]->lo > 1) --constrs[0]->lo; else ++constrs[0]->hi;
                constrs[0]->lit = lit_Undef;
                convertPbs(false);
                Lit newp = constrs[0]->lit;
                sat_solver.setFrozen(var(newp),true);
                sat_solver.addClause(~assump_ps.last(), newp);
                new_assump.push(assump_ps.last()); assump_ps.last() = newp;
                if (sat_solver.solveLimited(assump_ps) != l_False) break;
                found = false;
                for (int i=0; i < sat_solver.conflict.size(); i++)
                    if (assump_ps.last() == ~sat_solver.conflict[i]) { found = true; break;}
            }
        }
    }
    sat_solver.budgetOff(); sat_solver.verbosity = verb;
}

static inline int log2(int n) { int i=0; while (n>>=1) i++; return i; }

// add conflict kernels for uwr and constraints for scip
void MsSolver::add_benefit_constraint(vec<Pair<Lit,int> > &psCs,vec<bool> &model){
    int count=0; // record sat constri
    int count_unsat_constri = 0; // record unsat record
    if(use_add_constr){
        for (int i = 0; i < psCs.size(); i++)
        {
            Lit p = psCs[i].fst;
            bool in_harden = harden_lits.has(p);
            if (!in_harden)
            {
                if ((model[var(p)] && !sign(p)) || (!model[var(p)] && sign(p)))
                {
                    sat_clause_first.push(p);
                }
                else
                {
                    unsat_clause_first.push(p);
                    unsat_clause_second_Cs.push(Int(soft_cls[psCs[i].snd].fst));
                }
            }
        }
        srand(0);
        unsat_clause_first.copyTo(unsat_clause_second);
        std::random_shuffle(&unsat_clause_first[0], &unsat_clause_first[unsat_clause_first.size()]);
        double begin=cpuTime();
        double end;

        // executor unsat to sat add_const
        for(int i=0; i<unsat_clause_first.size(); i++){
            end=cpuTime();
            if(count > 100 || (end - begin >100))break;
            sat_clause_first.push(unsat_clause_first[i]);
            sat_solver.setConfBudget(1000);
            int verb = sat_solver.verbosity;
            sat_solver.verbosity = 0;
            if(sat_solver.solveLimited(sat_clause_first) == l_False){
                Minisat::vec<Lit> core_mus;
                std::vector<Lit> temp;
                for (int i = 0; i < sat_solver.conflict.size(); i++){
                    core_mus.push(~sat_solver.conflict[i]);
                    temp.push_back(sat_solver.conflict[i]);
                }
                constr_scip.push_back(temp);
                core_minimization(sat_solver, core_mus);
                if (core_mus.size() > 0 && core_mus.size() < 6){
                    count++;
                    sat_solver.addClause(core_mus);
                }
            }
            sat_solver.budgetOff();
            sat_solver.verbosity = verb;
            sat_clause_first.pop();
        }

        // executor unsat add_constr
        double begin_unsat_constri=cpuTime();
        double end_unsat_constri;
        while(count_unsat_constri < 100 && unsat_clause_second.size() > 0){
            end_unsat_constri=cpuTime();
            if(end_unsat_constri - begin_unsat_constri > 100)break;
            sat_solver.setConfBudget(1000);
            int verb = sat_solver.verbosity;
            sat_solver.verbosity = 0;
            auto status_unsat = sat_solver.solveLimited(unsat_clause_second);
            if( status_unsat == l_False){
                //add constri and removed conflicts clause
                assert(sat_solver.conflict.size() != 0);
                Minisat::vec<Lit> core_mus;
                std::vector<Lit> temp;
                for (int i = 0; i < sat_solver.conflict.size(); i++){
                    temp.push_back(sat_solver.conflict[i]);
                    core_mus.push(~sat_solver.conflict[i]);
                }
                constr_scip.push_back(temp);
                core_minimization(sat_solver, core_mus);
                if (core_mus.size() > 0 && core_mus.size() < 10){
                    count_unsat_constri++;
                    sat_solver.addClause(core_mus);
                }
                int removed = 0;
                int j;
                for (int i = 0; i < core_mus.size(); i++)
                {
                    Lit p = ~core_mus[i];
                    if ((j = bin_search(unsat_clause_second, p)) >= 0){
                        unsat_clause_second_Cs[j] = -unsat_clause_second_Cs[j];
                        removed++;
                    }
                }
                if(removed > 0){
                    int j = 0;
                    for (int i = 0; i < unsat_clause_second.size(); i++)
                    {
                        if(unsat_clause_second_Cs[i] < 0){
                            continue;
                        }
                        if( j < i ){
                            unsat_clause_second[j] = unsat_clause_second[i], unsat_clause_second_Cs[j] = unsat_clause_second_Cs[i];
                        }
                        j++;
                    }
                }
                if ((removed = unsat_clause_second.size() - j) > 0)
                    unsat_clause_second.shrink(removed), unsat_clause_second_Cs.shrink(removed);
            }else if(status_unsat == l_True){
                sat_solver.budgetOff();
                sat_solver.verbosity = verb;
                break;
            }
            sat_solver.budgetOff();
            sat_solver.verbosity = verb;
        }
    }
    printf("unsat_to_sat add_constr =: %d,   unsat add_constr =:  %d, total =:  %d \n",count_unsat_constri,count,count_unsat_constri + count);
}

void MsSolver::satlike_solve(vec<bool> &model){
    int c = satlike.num_hclauses;
    satlike.num_sclauses = soft_cls.size();
    satlike.num_clauses = satlike.num_hclauses + satlike.num_sclauses;

    for (int i = 0; i < soft_cls.size(); i++)
    {
        satlike.org_clause_weight[c + i] = soft_cls[i].fst;
        if (soft_cls[i].snd->size() == 1)
            satlike.clause_lit_count[c + i] = soft_cls[i].snd->size();
        else
            satlike.clause_lit_count[c + i] = soft_cls[i].snd->size() - 1;

        satlike.clause_lit[c + i] = new mylit[satlike.clause_lit_count[c + i] + 1];
        int j;
        for (j = 0; j < satlike.clause_lit_count[c + i]; ++j)
        {
            satlike.clause_lit[c + i][j].clause_num = c + i;
            satlike.clause_lit[c + i][j].var_num = var((*soft_cls[i].snd)[j]) + 1;
            satlike.clause_lit[c + i][j].sense = (1 - sign((*soft_cls[i].snd)[j]));
            satlike.var_lit_count[var((*soft_cls[i].snd)[j]) + 1]++;
        }
        satlike.clause_lit[c + i][j].var_num = 0;
        satlike.clause_lit[c + i][j].clause_num = -1;
    }
    satlike.build_instance();
    Minisat::vec<Lit> empty_assumpt;
    std::cout << "c changing to satlike solver!!!" << std::endl;
    std::vector<int> init_solu(satlike.num_vars + 1);
    if(use_hard_clause_value_init){
        if(sat_solver.solveLimited(empty_assumpt) == l_True){
            satlike.settings();
            for (Var x = 0; x < satlike.num_vars; x++)
                init_solu[x + 1] = (sat_solver.model[x] == l_True);
        }
    }
    satlike.init(init_solu);
    start_timing();
    int time_limit_for_ls = 15;
    int step;
    if (satlike.if_using_neighbor)
    {
        for (step = 1; step < satlike.max_flips; ++step)
        {
            if (satlike.hard_unsat_nb == 0 &&
                (satlike.soft_unsat_weight < satlike.opt_unsat_weight || satlike.best_soln_feasible == 0))
            {
                satlike.max_flips = step + satlike.max_non_improve_flip;
                time_limit_for_ls = get_runtime() + 15;
                if (satlike.soft_unsat_weight < satlike.opt_unsat_weight)
                {
                    satlike.best_soln_feasible = 1;
                    satlike.opt_unsat_weight = satlike.soft_unsat_weight;
                    //std::cout << "c step " << step << std::endl;
                    std::cout << "c satlike opt unsat weight: " << satlike.opt_unsat_weight << std::endl;
                    for (int v = 1; v <= satlike.num_vars; ++v)
                        satlike.best_soln[v] = satlike.cur_soln[v];
                }
                if (satlike.opt_unsat_weight == 0)
                    break;
            }
            int flipvar = satlike.pick_var();
            satlike.flip(flipvar);
            satlike.time_stamp[flipvar] = step;

            if (step % 1000 == 0)
            {
                if (get_runtime() > time_limit_for_ls || get_runtime() > 300)
                    break;
            }
        }
    }
    else
    {
        for (step = 1; step < satlike.max_flips; ++step)
        {
            if (satlike.hard_unsat_nb == 0 &&
                (satlike.soft_unsat_weight < satlike.opt_unsat_weight || satlike.best_soln_feasible == 0))
            {
                satlike.max_flips = step + satlike.max_non_improve_flip;
                time_limit_for_ls = get_runtime() + 15;
                if (satlike.soft_unsat_weight < satlike.opt_unsat_weight)
                {
                    satlike.best_soln_feasible = 1;
                    satlike.opt_unsat_weight = satlike.soft_unsat_weight;
                    //std::cout << "c step " << step << std::endl;
                    std::cout << "c satlike opt unsat weight: " << satlike.opt_unsat_weight << std::endl;
                    //satlike.verify_sol();
                    for (int v = 1; v <= satlike.num_vars; ++v)
                        satlike.best_soln[v] = satlike.cur_soln[v];
                }
                if (satlike.opt_unsat_weight == 0)
                    break;
            }
            int flipvar = satlike.pick_var();
            satlike.flip2(flipvar);
            satlike.time_stamp[flipvar] = step;

            if (step % 1000 == 0)
            {
                if (get_runtime() > time_limit_for_ls || get_runtime() > 300)
                    break;
            }
        }
    }
    std::cout << "c satlike search done!" << std::endl;
    if(!satlike.verify_sol()){
        printf("verify_sol failed turn to satlike_broken\n");
        return;
    }

    std::cout << "c soft clause size=" << soft_cls.size() << std::endl;
    Minisat::vec<Lit> soft_unsat;
    for (int v = 0; v < satlike.num_vars; ++v)
        model.push(satlike.best_soln[v + 1]);
    for (Var x = satlike.num_vars; x < pb_n_vars; x++)
        assert(sat_solver.model[x] != l_Undef),
                model.push(sat_solver.model[x] == l_True);

    for (int i = 0; i < soft_cls.size(); i++)
    {
        if (soft_cls[i].snd->size() > 1)
        {
            Lit relax =(soft_cls[i].snd->last());
            if (satisfied_soft_cls(soft_cls[i].snd, model))
            {
                model[var(relax)] = sign(relax);
            }
            else
            {
                model[var(relax)] = !sign(relax);
            }
        }
    }
    model.growTo(model.size()+am1_cls.size());

    for (int i = 0; i < am1_cls.size(); ++i)
    {
        bool ifs = false;
        for (int j = 0; j < am1_cls[i].size() - 1; ++j)
        {
            Lit relax=am1_cls[i][j];
            if (model[var(relax)] && !sign(relax) || !model[var(relax)] && sign(relax))
            {
                ifs = true;
                break;
            }
        }
        Lit temp = am1_cls[i][am1_cls[i].size() - 1];
        if (ifs)
        {
            model[var(temp)] = sign(temp);
        }
        else
            model[var(temp)] = !sign(temp);
    }
    std::cout << "c lb=" << tolong(LB_goalvalue) << " ub=" << tolong(UB_goalvalue) << std::endl;
    goalvalue_satlike = evalGoal(soft_cls, model, soft_unsat) + fixed_goalval;
    if (goalvalue_satlike < best_goalvalue)
    {
        best_goalvalue = goalvalue_satlike;
        model.copyTo(best_model);
        for(int i=0; i< model.size(); i++){
            model_value += toString(model[i]);
        }
    }
    std::cout << "c get satlike search result" << "goal value=: " << tolong(goalvalue_satlike)<< std::endl;
}

template<class T>
SCIP_RETCODE add_constr(SCIP *scip,
                        const T &ps,
                        const std::vector<SCIP_VAR *> &vars,
                        const std::string &const_name)
{
    SCIP_CONS *cons = nullptr;
    SCIP_CALL(SCIPcreateConsBasicLinear(scip, &cons, const_name.c_str(), 0, nullptr, nullptr, 0, SCIPinfinity(scip)));
    int lhs = 1;
    for (int j = 0; j < ps.size(); j++)
    {
        auto lit = ps[j];
        auto v = vars[var(lit)];
        SCIP_CALL(SCIPaddCoefLinear(scip, cons, v, sign(lit) ? -1 : 1));
        if (sign(lit))
            lhs--;
    }
    SCIP_CALL(SCIPchgLhsLinear(scip, cons, lhs));
    SCIP_CALL(SCIPaddCons(scip, cons));
    SCIP_CALL(SCIPreleaseCons(scip, &cons));
    return SCIP_OKAY;
}

SCIP_RETCODE init_sol(SCIP *scip, const std::vector<SCIP_VAR *> &vars,std::string &values)
{
    assert(vars.size() == values.size());
    SCIP_SOL *sol;
    SCIP_CALL(SCIPcreateSol(scip, &sol, NULL));
    for (int i = 0; i < vars.size(); i++)
        SCIP_CALL(SCIPsetSolVal(scip, sol, vars[i], values[i] - '0'));
    SCIP_Bool stored;
    SCIP_CALL(SCIPaddSol(scip, sol, &stored));
    std::cout << "init solution " << (stored ? "success\n" : "failed\n");
    SCIP_CALL(SCIPfreeSol(scip, &sol));
    return SCIP_OKAY;
}

SCIP_RETCODE MsSolver::scip_solve(const Minisat::vec<Lit> &assump_ps,
                                  const vec<Int> &assump_Cs,
                                  const IntLitQueue &delayed_assump,
                                  bool weighted_instance,
                                  bool &found_opt)
{
    // 1. create scip context object
    SCIP *scip = nullptr;
    SCIP_CALL(SCIPcreate(&scip));
    SCIP_CALL(SCIPincludeDefaultPlugins(scip));
    SCIP_CALL(SCIPcreateProbBasic(scip, "CASHWMaxSat"));
    SCIP_CALL(SCIPsetRealParam(scip, "limits/time", 600));
    if (opt_verbosity == 0)
        SCIP_CALL(SCIPsetIntParam(scip, "display/verblevel", 0));

    // 2. create variable(include relax)
    std::vector<SCIP_VAR *> vars;
    for (Var v = 0; v < sat_solver.nVars(); ++v)
    {
        SCIP_VAR *var = nullptr;
        std::string name = "x" + std::to_string(v + 1);
        SCIP_Real lb = 0, ub = 1;
        if (value(v) == l_False) ub = 0;
        else if (value(v) == l_True) lb = 1;
        SCIP_CALL(SCIPcreateVarBasic(scip, &var, name.c_str(), lb, ub, 0, SCIP_VARTYPE_BINARY));
        SCIP_CALL(SCIPaddVar(scip, var));
        vars.push_back(var);
    }

    // 3. add constraint
    for (int i = 0; i < sat_solver.nClauses(); i++)
    {
        bool is_satisfied;
        const Minisat::Clause &ps = sat_solver.GetClause(i, is_satisfied);
        if (!is_satisfied)
        {
            std::string cons_name = "cons" + std::to_string(i);
            add_constr(scip, ps, vars, cons_name);
        }
    }
    weight_t obj_offset = 0;
    auto set_var_coef = [&vars, &obj_offset, scip, this](Lit relax, weight_t weight)
    {
        weight_t coef = sign(relax) ? weight : -weight;
        coef *= this->goal_gcd;
        SCIP_CALL(SCIPaddVarObj(scip, vars[var(relax)], coef));
        if (coef < 0)
            obj_offset += abs(coef);
    };

    if(!constr_scip.empty()){
        for(int i=0; i<constr_scip.size(); i++){
            std::vector<Lit> &constr = constr_scip.at(i);
            std::string cons_name = "satlike_constraint" + std::to_string(i + sat_solver.nClauses());
            add_constr(scip, constr, vars, cons_name);
        }
    }

    if (weighted_instance)
    {
        for (int i = 0; i < top_for_strat; ++i)
        {
            const Pair<weight_t, Minisat::vec<Lit> *> &weight_ps = soft_cls[i];
            const Minisat::vec<Lit> &ps = *(weight_ps.snd);
            auto relax = ps.last();
            if (ps.size() > 1) relax = ~relax;
            weight_t weight = weight_ps.fst;
            set_var_coef(relax, weight);
            if (ps.size() > 1)
            {
                std::string cons_name = "soft_cons" + std::to_string(i);
                add_constr(scip, ps, vars, cons_name);
            }
        }
    }

    // 4. set objective
    reportf("assump_ps.size=%u\n", assump_ps.size());
    for (int i = 0; i < assump_ps.size(); ++i)
        set_var_coef(assump_ps[i], tolong(assump_Cs[i]));
    reportf("delayed_assump.size=%u\n", delayed_assump.getHeap().size() - 1);
    for (int i = 1; i < delayed_assump.getHeap().size(); ++i)
    {
        const Pair<Int, Lit> &weight_lit = delayed_assump.getHeap()[i];
        Lit relax = weight_lit.snd;
        weight_t weight = tolong(weight_lit.fst);
        set_var_coef(relax, weight);
    }
    // create a var for the fixed part of objective
    reportf("obj_offset=%ld\n", obj_offset);
    obj_offset += tolong(LB_goalvalue) * goal_gcd;
    if (obj_offset != 0)
    {
        SCIP_VAR *var = nullptr;
        SCIP_CALL(SCIPcreateVarBasic(scip, &var, "obj_offset", 1, 1, obj_offset, SCIP_VARTYPE_BINARY));
        SCIP_CALL(SCIPaddVar(scip, var));
        vars.push_back(var);
        model_value += "1";
    }

    //5. set init sol
    if(!model_value.empty()){
        init_sol(scip,vars,model_value);
    }

    // 6. do solve
    // SCIP_CALL((SCIPwriteOrigProblem(scip, "1.lp", nullptr, FALSE)));
    // SCIP_CALL((SCIPwriteTransProblem(scip, "2.lp", nullptr, FALSE)));
    reportf("start SCIPsolve()...\n");
    SCIP_CALL(SCIPsolve(scip));
    if (SCIP_STATUS_OPTIMAL == SCIPgetStatus(scip))
    {
        found_opt = true;
        SCIP_SOL *sol = SCIPgetBestSol(scip);
        assert(sol != NULL);
        // SCIP_CALL(SCIPprintSol(scip, sol, NULL, FALSE));
        best_goalvalue = long(round(SCIPgetSolOrigObj(scip, sol)));
        reportf("SCIPgetSolOrigObj = %ld\n", tolong(best_goalvalue));
        best_model.clear();
        for (Var x = 0; x < pb_n_vars; x++)
        {
            SCIP_Real v = SCIPgetSolVal(scip, sol, vars[x]);
            best_model.push(v > 0.5);
        }
    } else
        found_opt = false;

    // 7. release
    for (auto v: vars)
        SCIP_CALL(SCIPreleaseVar(scip, &v));
    vars.clear();
    SCIP_CALL(SCIPfree(&scip));
    return SCIP_OKAY;
}

void print_Lits(const char *s, const Minisat::vec<Lit> &ps, bool print_data = false, bool sort = false)
{
    Minisat::vec<Lit> ps1;
    ps.copyTo(ps1);
    std::sort(&ps1[0], &ps1[ps1.size()]);
    reportf("%s: (size=%d) {", s, ps1.size());
    if (print_data)
        for (int i = 0; i < ps1.size(); ++i)
            reportf("%c%d,", sign(ps1[i]) ? '-' : ' ', var(ps1[i]) + 1);
    reportf("},\n");
}

void MsSolver::maxsat_solve(solve_Command cmd)
{
    if (!okay()) {
        if (opt_verbosity >= 1) sat_solver.printVarsCls();
        return;
    }
#if defined(GLUCOSE3) || defined(GLUCOSE4)    
    if (opt_verbosity >= 1) sat_solver.verbEveryConflicts = 100000;
    sat_solver.setIncrementalMode();
#endif
    if (soft_cls.size() == 0) { opt_maxsat_msu = false; solve(cmd); return; }
    // Convert constraints:
    pb_n_vars = nVars();
    pb_n_constrs = nClauses();
    if (constrs.size() > 0) {
        if (opt_verbosity >= 1)
            reportf("Converting %d PB-constraints to clauses...\n", constrs.size());
        propagate();
        if (!convertPbs(true)){
            if (opt_verbosity >= 1) sat_solver.printVarsCls(constrs.size() > 0);
            assert(!okay()); return;
        }
    }

    // Freeze goal function variables (for SatELite):
    for (int i = 0; i < soft_cls.size(); i++) {
        sat_solver.setFrozen(var(soft_cls[i].snd->last()), true);
        if (opt_output_top > 0)
            for (int j = soft_cls[i].snd->size() - 2; j >= 0; j--) 
                sat_solver.setFrozen(var((*soft_cls[i].snd)[j]), true);
    }
    sat_solver.verbosity = opt_verbosity - 1;

    goal_gcd = soft_cls[0].fst;
    for (int i = 1; i < soft_cls.size() && goal_gcd != 1; ++i) goal_gcd = gcd(goal_gcd, soft_cls[i].fst);
    if (goal_gcd != 1) {
        if (LB_goalvalue != Int_MIN) LB_goalvalue /= Int(goal_gcd);
        if (UB_goalvalue != Int_MAX) UB_goalvalue /= Int(goal_gcd);
    }

    assert(best_goalvalue == Int_MAX);

    if (opt_convert_goal != ct_Undef)
        opt_convert = opt_convert_goal;
    opt_sort_thres *= opt_goal_bias;
    opt_shared_fmls = true;

    if (opt_cnf != NULL)
        reportf("Exporting CNF to: \b%s\b\n", opt_cnf),
        sat_solver.toDimacs(opt_cnf),
        exit(0);

    pb_solver = this;
    signal(SIGINT, SIGINT_interrupt);
#ifdef SIGXCPU
    signal(SIGXCPU,SIGINT_interrupt);
#endif

    Map<int,int> assump_map(-1);
    vec<Linear*> saved_constrs;
    vec<Lit> goal_ps;
    Minisat::vec<Lit> assump_ps;
    vec<Int> assump_Cs, goal_Cs, saved_constrs_Cs;
    vec<weight_t> sorted_assump_Cs;
    vec<Pair<Int, bool> > sum_sorted_soft_cls;
    bool    sat = false, weighted_instance = true;
    Lit assump_lit = lit_Undef, max_assump = lit_Undef;
    Int     try_lessthan = opt_goal, max_assump_Cs = Int_MIN;
    int     n_solutions = 0;    // (only for AllSolutions mode)
    vec<Pair<Lit,int> > psCs;
    vec<bool> multi_level_opt;
    bool opt_delay_init_constraints = false, 
         opt_core_minimization = (nClauses() > 0 || soft_cls.size() < 100000);
    IntLitQueue delayed_assump;
    Int delayed_assump_sum = 0;
    BitMap top_impl_gen(true);
    vec<Int> top_UB_stack;
    bool optimum_found = false;

    Int LB_goalval = 0, UB_goalval = 0;    
    sort(&soft_cls[0], soft_cls.size(), LT<Pair<weight_t, Minisat::vec<Lit>*> >());
    int j = 0; Lit pj;
    for (int i = 0; i < soft_cls.size(); ++i) {
        soft_cls[i].fst /= goal_gcd;
        if (soft_cls[i].fst < 0) { 
            fixed_goalval += soft_cls[i].fst; soft_cls[i].fst = -soft_cls[i].fst; soft_cls[i].snd->last() = ~soft_cls[i].snd->last(); 
        }
        Lit p = soft_cls[i].snd->last();
        if (soft_cls[i].snd->size() == 1) p = ~p;
        if (value(p) != l_Undef) {
            if (value(p) == l_True) {
                fixed_goalval += soft_cls[i].fst;
                addUnit(p);
            } else {
                if (soft_cls[i].snd->size() > 1) sat_solver.addClause(*soft_cls[i].snd);
                addUnit(~p);
            }
        } else if (j > 0 && p == pj)  
            soft_cls[j-1].fst += soft_cls[i].fst;
        else if (j > 0 && p == ~pj) {
            fixed_goalval += (soft_cls[j-1].fst < soft_cls[i].fst ? soft_cls[j-1].fst : soft_cls[i].fst); 
            soft_cls[j-1].fst -= soft_cls[i].fst;
            if (soft_cls[j-1].fst < 0) soft_cls[j-1].fst = -soft_cls[j-1].fst, soft_cls[j-1].snd->last() = pj, pj = ~pj; 
        } else {
            if (j > 0 && soft_cls[j-1].fst == 0) j--;
            if (j < i) soft_cls[j] = soft_cls[i];
            pj = p; j++;
        }
    }
    if (j < soft_cls.size()) soft_cls.shrink(soft_cls.size() - j);
    top_for_strat = top_for_hard = soft_cls.size();
    sort(soft_cls);
    weighted_instance = (soft_cls.size() > 1 && soft_cls[0].fst != soft_cls.last().fst);
    for (int i = 0; i < soft_cls.size(); i++) {
        Lit p = soft_cls[i].snd->last();
        psCs.push(Pair_new(soft_cls[i].snd->size() == 1 ? p : ~p, i));
        if (weighted_instance) sorted_assump_Cs.push(soft_cls[i].fst);
        UB_goalval += soft_cls[i].fst;
    }
    LB_goalval += fixed_goalval, UB_goalval += fixed_goalval;
    sort(psCs);
    if (weighted_instance) sortUnique(sorted_assump_Cs);
    if (LB_goalvalue < LB_goalval) LB_goalvalue = LB_goalval;
    if (UB_goalvalue == Int_MAX)   UB_goalvalue = UB_goalval;
    else {
        for (int i = 0; i < psCs.size(); i++)
            goal_ps.push(~psCs[i].fst), goal_Cs.push(soft_cls[psCs[i].snd].fst);
        if (try_lessthan == Int_MAX) try_lessthan = ++UB_goalvalue;
        if (goal_ps.size() > 0) {
            addConstr(goal_ps, goal_Cs, try_lessthan - fixed_goalval, -2, assump_lit);
            convertPbs(false);
        }
    }
    if (opt_minimization != 1 || sorted_assump_Cs.size() == 0) {
        for (int i = 0; i < psCs.size(); i++)
            assump_ps.push(psCs[i].fst), assump_Cs.push(Int(soft_cls[psCs[i].snd].fst));
        for (int i = 0; i < soft_cls.size(); i++) { 
            if (soft_cls[i].snd->size() > 1) sat_solver.addClause(*soft_cls[i].snd);
        }
        top_for_strat = top_for_hard = 0;
    } else {
        for (int i = soft_cls.size() - 1; i >= 0; i--) 
            for (int j = soft_cls[i].snd->size() - 1; j >= 0; j--) 
                sat_solver.setFrozen(var((*soft_cls[i].snd)[j]), true);
        Int sum = 0;
        int ml_opt = 0;
        multi_level_opt.push(false); sum_sorted_soft_cls.push(Pair_new(0, true));
        for (int i = 0, cnt = 0, sz = sorted_assump_Cs.size(), j = 1; j < sz; j++) {
            while (i < soft_cls.size() && soft_cls[i].fst < sorted_assump_Cs[j])
                sum += soft_cls[i++].fst, cnt++;
            sum_sorted_soft_cls.push(Pair_new(sum, sum < sorted_assump_Cs[j]));
            multi_level_opt.push(sum < sorted_assump_Cs[j]);
            if (multi_level_opt.last()) ml_opt++;
        }
        opt_stratification(sorted_assump_Cs, sum_sorted_soft_cls);
        opt_lexicographic = (opt_output_top < 0); // true;
        if (opt_verbosity >= 1 && ml_opt > 0 && opt_output_top < 0) 
            reportf("Boolean lexicographic optimization can be done in %d point(s).%s\n", 
                    ml_opt, (opt_lexicographic ? "" : " Try -lex-opt option."));
        max_assump_Cs = do_stratification(sat_solver, sorted_assump_Cs, soft_cls, top_for_strat, assump_ps, assump_Cs);
    }
    if (psCs.size() > 0) max_assump = psCs.last().fst;
    if (opt_minimization == 1 && opt_maxsat_prepr) 
        preprocess_soft_cls(assump_ps, assump_Cs, max_assump, max_assump_Cs, delayed_assump, delayed_assump_sum);
    if (opt_verbosity >= 1)
        sat_solver.printVarsCls(goal_ps.size() > 0, &soft_cls, top_for_strat);

    if (opt_polarity_sug != 0)
        for (int i = 0; i < soft_cls.size(); i++){
            Lit p = soft_cls[i].snd->last(); if (soft_cls[i].snd->size() == 1) p = ~p;
            bool dir = opt_polarity_sug > 0 ? !sign(p) : sign(p);
            sat_solver.setPolarity(var(p), LBOOL(dir));
        }
    bool first_time = false;
    if (opt_cpu_lim != INT32_MAX) {
        int used_cpu = cpuTime();
        first_time=true; limitTime(used_cpu + (opt_cpu_lim - used_cpu)/4);
    }

    // Try to use satlike to obtain efficient feasible solutions
    if(satlike_is_use){
        vec<bool> model_satlike;
        satlike_solve(model_satlike);
        add_benefit_constraint(psCs,model_satlike);
    }
    // use scip to solve
    if (pb_n_vars < 100000 && pb_n_constrs < 100000 && soft_cls.size() < 100000)
    {
        bool found_opt = false;
        reportf("use SCIP solver, version 7.0.2, https://www.scipopt.org\n");
        SCIP_RETCODE ret = scip_solve(assump_ps, assump_Cs, delayed_assump, weighted_instance, found_opt);
        if (ret == SCIP_OKAY && found_opt)
            return;
        else
            reportf("scip timeout\n");
    }

    bool enable_multi_solve = !weighted_instance;
    int multi_solve_num_limit = 50;
    int multi_solve_time_limit = 60; // seconds
    bool enable_dynamic_delay = !weighted_instance;
    int dynamic_delay_core_threshoad = 5;
    bool enable_delay_pop_one = !weighted_instance;
    delayed_assump.weighted_instance = weighted_instance;
    
    lbool status;
    int cn = 0;
    while (1) {
      cn++;
      if (use_base_assump) for (int i = 0; i < base_assump.size(); i++) assump_ps.push(base_assump[i]);
      auto begin = cpuTime();
      status = 
          base_assump.size() == 1 && base_assump[0] == assump_lit ? l_True :
          base_assump.size() == 1 && base_assump[0] == ~assump_lit ? l_False :
          sat_solver.solveLimited(assump_ps);
      auto end = cpuTime();
      auto _1st_solve_time = end - begin;
      if(opt_verbosity) reportf("cn=%d status=%s time=%.1f\n", cn, status==l_True?"SAT":"UnSAT", _1st_solve_time);
      if(opt_verbosity) print_Lits("core", sat_solver.conflict, false);
      if (use_base_assump) {
          for (int i = 0; i < base_assump.size(); i++) {
              if (status == l_True && var(base_assump[i]) < pb_n_vars) addUnit(base_assump[i]);
              assump_ps.pop();
          }
          if (status != l_Undef) base_assump.clear();
      }
      if (first_time) { 
        first_time = false; sat_solver.clearInterrupt(); 
        if (asynch_interrupt && cpu_interrupt) asynch_interrupt = false;
        cpu_interrupt = false; limitTime(opt_cpu_lim);
        if (status == l_Undef) continue;
      }
      if (status  == l_Undef) {
        if (asynch_interrupt) { reportf("*** Interrupted ***\n"); break; }
      } else if (status == l_True) { // SAT returned
        if (opt_minimization == 1 && opt_delay_init_constraints) {
            opt_delay_init_constraints = false;
            convertPbs(false);
            constrs.clear();
            continue;
        }
        Int lastCs = 1;
        if(opt_minimization != 1 && assump_ps.size() == 1 && assump_ps.last() == assump_lit) {
          addUnit(assump_lit);
          lastCs = assump_Cs.last();
          assump_ps.pop(); assump_Cs.pop(); assump_lit = lit_Undef;
        }
        sat = true;

        if (cmd == sc_AllSolutions){
            Minisat::vec<Lit>    ban;
            n_solutions++;
            reportf("MODEL# %d:", n_solutions);
            for (Var x = 0; x < pb_n_vars; x++){
                assert(sat_solver.modelValue(x) != l_Undef);
                ban.push(mkLit(x, sat_solver.modelValue(x) == l_True));
                if (index2name[x][0] != '#')
                    reportf(" %s%s", (sat_solver.modelValue(x) == l_False)?"-":"", index2name[x]);
            }
            reportf("\n");
            sat_solver.addClause_(ban);
        }else{
            vec<bool> model;
            Minisat::vec<Lit> soft_unsat;
            for (Var x = 0; x < pb_n_vars; x++)
                assert(sat_solver.modelValue(x) != l_Undef),
                model.push(sat_solver.modelValue(x) == l_True);
            for (int i = 0; i < top_for_strat; i++)
                if (soft_cls[i].snd->size() > 1)
                    model[var(soft_cls[i].snd->last())] = !sign(soft_cls[i].snd->last());
            Int goalvalue = evalGoal(soft_cls, model, soft_unsat) + fixed_goalval;
            extern bool opt_satisfiable_out;
            if (goalvalue < best_goalvalue || opt_output_top > 0 && goalvalue == best_goalvalue) {
                best_goalvalue = goalvalue;
                model.moveTo(best_model);
                char* tmp = toString(best_goalvalue * goal_gcd);
                if (opt_satisfiable_out && opt_output_top < 0 && (opt_satlive || opt_verbosity == 0))
                    printf("o %s\n", tmp), fflush(stdout);
                else if (opt_verbosity > 0 || !opt_satisfiable_out) 
                    reportf("%s solution: %s\n", (optimum_found ? "Next" : "Found"), tmp);
                xfree(tmp);
            } else model.clear(); 
            if (best_goalvalue < UB_goalvalue && opt_output_top < 0) UB_goalvalue = best_goalvalue;
            else if (opt_output_top > 1) {
                while (top_UB_stack.size() > 0 && top_UB_stack.last() < best_goalvalue) top_UB_stack.pop();
                if (top_UB_stack.size() == 0 || top_UB_stack.last() > best_goalvalue) top_UB_stack.push(best_goalvalue);
                if (top_UB_stack.size() >= opt_output_top) {
                    Int &bound = top_UB_stack[top_UB_stack.size() - opt_output_top];
                    if (bound < UB_goalvalue) UB_goalvalue = bound;
                }
            }
            if (cmd == sc_FirstSolution || (opt_minimization == 1 || UB_goalvalue == LB_goalvalue) &&
                                           sorted_assump_Cs.size() == 0 && delayed_assump.empty())
                if (opt_minimization == 1 && opt_output_top > 0) {
                    outputResult(*this, false);
                    if (opt_verbosity > 0 && !optimum_found) {
                        optimum_found = true;
                        char* tmp = toString(best_goalvalue * goal_gcd);
                        reportf(" OPT SOLUTION: %s\n", tmp);
                        xfree(tmp);
                    }
                    if (--opt_output_top == 0) break;
                    else { 
                        best_goalvalue = Int_MAX;
                        if (soft_unsat.size() > 0) sat_solver.addClause(soft_unsat);
                        else { status = l_False; break; }
                        for (int i = 0; i < soft_cls.size(); i++)
                            if (soft_unsat[i] == soft_cls[i].snd->last() && soft_cls[i].snd->size() > 1 && 
                                    top_impl_gen.at(var(soft_unsat[i]))) {
                                top_impl_gen.set(var(soft_unsat[i]), false);
                                for (int j = soft_cls[i].snd->size() - 2; j >= 0; j--)
                                    sat_solver.addClause(~soft_unsat[i], ~(*soft_cls[i].snd)[j]);
                            }
                        continue;
                    }
                } else break;
            if (opt_minimization == 1) {
                assert(sorted_assump_Cs.size() > 0 || !delayed_assump.empty()); 
                int old_top = top_for_strat;
                if (delayed_assump.empty() || sorted_assump_Cs.size() > 0 && Int(sorted_assump_Cs.last()) > delayed_assump.top().fst) {
                    if (opt_lexicographic && multi_level_opt[sorted_assump_Cs.size()]) {
                        Int bound = sum_sorted_soft_cls[sorted_assump_Cs.size()].fst + delayed_assump_sum;
                        int cnt_assump = 0;
                        for (int i = 0; i < assump_ps.size() && assump_ps[i] <= max_assump; i++)
                            if (assump_Cs[i] > bound)
                                addUnit(assump_ps[i]), assump_Cs[i] = -assump_Cs[i], cnt_assump++;
                        if (cnt_assump > 0) {
                            clear_assumptions(assump_ps, assump_Cs);
                            if (opt_verbosity > 0) reportf("Boolean lexicographic optimization - done.\n");
                        }
                    }
                    max_assump_Cs = do_stratification(sat_solver, sorted_assump_Cs, soft_cls, top_for_strat, assump_ps, assump_Cs);
                } else {
                    max_assump_Cs = delayed_assump.top().fst;
                    vec<Pair<Lit, Int> > new_assump;
                    do { 
                        new_assump.push(Pair_new(delayed_assump.top().snd, max_assump_Cs));
                        delayed_assump_sum -= delayed_assump.top().fst;
                        delayed_assump.pop(); 
                        if(enable_delay_pop_one) break;
                    } while (!delayed_assump.empty() && delayed_assump.top().fst >= max_assump_Cs);
                    sort(new_assump); int sz = new_assump.size();
                    assump_ps.growTo(assump_ps.size() + sz); assump_Cs.growTo(assump_Cs.size() + sz);
                    for (int i = assump_ps.size() - 1; i >= sz; i--)
                        assump_ps[i] = assump_ps[i-sz], assump_Cs[i] = assump_Cs[i-sz];
                    for (int fr = sz, to = 0, i = 0; i < new_assump.size(); i++) {
                        Lit p = new_assump[i].fst;
                        while (fr < assump_ps.size() && assump_ps[fr] <= p)
                            assump_ps[to] = assump_ps[fr], assump_Cs[to++] = assump_Cs[fr++];
                        assump_ps[to] = p; assump_Cs[to++] = new_assump[i].snd;
                    }
                }
                harden_soft_cls(assump_ps, assump_Cs);
                if (top_for_strat < old_top) {
                    try_lessthan = best_goalvalue;
                    if (opt_maxsat_prepr) 
                        preprocess_soft_cls(assump_ps, assump_Cs, max_assump, max_assump_Cs, delayed_assump, delayed_assump_sum);
                }
                continue;
            } else harden_soft_cls(assump_ps, assump_Cs);
            if (opt_minimization == 0 || best_goalvalue - LB_goalvalue < opt_seq_thres) {
                assump_lit = (assump_ps.size() == 0 ? lit_Undef : mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true));
                try_lessthan = best_goalvalue;
            } else {
                assump_lit = assump_lit == lit_Undef || !use_base_assump ?
                    mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars)) : assump_lit;
                try_lessthan = (LB_goalvalue*(100-opt_bin_percent) + best_goalvalue*(opt_bin_percent))/100;
            }
            Int goal_diff = harden_goalval+fixed_goalval;
            if (!addConstr(goal_ps, goal_Cs, try_lessthan - goal_diff, -2, assump_lit))
                break; // unsat
            if (assump_lit != lit_Undef && !use_base_assump) {
                sat_solver.setFrozen(var(assump_lit),true);
                assump_ps.push(assump_lit), assump_Cs.push(opt_minimization == 2 ? try_lessthan : lastCs);
            }
            convertPbs(false);
        }
      } else { // UNSAT returned
        if (assump_ps.size() == 0 && assump_lit == lit_Undef) break;
        {
        
        if(enable_multi_solve && _1st_solve_time < 20 && sat_solver.conflict.size() >= 4)
        {
            Minisat::vec<Lit> assump_tmp, bestConfict;
            assump_ps.copyTo(assump_tmp);
            sat_solver.conflict.copyTo(bestConfict);

            if(opt_verbosity) reportf("Second solve...\n");
            int solve_cn = 0;
            auto _2nd_solve_begin = cpuTime();
            srand(0);
            while(solve_cn < multi_solve_num_limit || (cpuTime() - _2nd_solve_begin) < _1st_solve_time)
            {
                if((cpuTime() - _2nd_solve_begin) > multi_solve_time_limit)   break;
                if(solve_cn > 10000) break;
                solve_cn++;
                if(solve_cn == 1)
                    sat_solver.increased_assump_bcp = true;
                else
                    std::random_shuffle(&assump_tmp[0], &assump_tmp[assump_tmp.size()]);
                lbool res = sat_solver.solveLimited(assump_tmp);
                if(solve_cn == 1) sat_solver.increased_assump_bcp = false;
                assert(res == l_False);
                if(bestConfict.size() > sat_solver.conflict.size() )
                    sat_solver.conflict.copyTo(bestConfict);
                if(bestConfict.size() == 1) break;
            }
            if(opt_verbosity) reportf("%d solves done in %.1fs\n", multi_solve_num_limit, cpuTime() - _2nd_solve_begin);
            if(opt_verbosity) reportf("bestUnminimizedConflict.size = %d\n", bestConfict.size());
            bestConfict.copyTo(sat_solver.conflict);
        }
            
        Minisat::vec<Lit> core_mus;
        if (opt_core_minimization) {
            if (weighted_instance) {
                vec<Pair<Pair<Int, int>, Lit> > Cs_mus;
                for (int i = 0; i < sat_solver.conflict.size(); i++) {
                    Lit p = ~sat_solver.conflict[i];
                    int j = bin_search(assump_ps, p);
                    Cs_mus.push(Pair_new(Pair_new((j>=0 ? assump_Cs[j] : 0),i),p));
                }
                sort(Cs_mus);
                for (int i = 0; i < Cs_mus.size(); i++) core_mus.push(Cs_mus[i].snd);
            } else
            {
                if (sat_solver.conflict.size() > 0)
                    std::sort(&sat_solver.conflict[0], &sat_solver.conflict[sat_solver.conflict.size()], std::greater<Lit>());
                for (int i = 0; i < sat_solver.conflict.size(); i++) core_mus.push(~sat_solver.conflict[i]);
            }
            core_minimization(sat_solver, core_mus, weighted_instance?1000:2000);
        } else
            for (int i = 0; i < sat_solver.conflict.size(); i++) core_mus.push(sat_solver.conflict[i]);
        if(opt_verbosity) print_Lits("core_mus", core_mus, false);
        if (core_mus.size() > 0 && core_mus.size() < 6) sat_solver.addClause(core_mus);
        Int min_removed = Int_MAX, min_bound = Int_MAX;
        int removed = 0;
        bool other_conflict = false;

        if (opt_minimization == 1) { 
            goal_ps.clear(); goal_Cs.clear();
        }
        for (int j, i = 0; i < core_mus.size(); i++) {
            Lit p = ~core_mus[i];
            if ((j = bin_search(assump_ps, p)) >= 0) { 
                if (opt_minimization == 1 || p <= max_assump) {
                    goal_ps.push(~p), goal_Cs.push(opt_minimization == 1 ? 1 : assump_Cs[j]);
                    if (assump_Cs[j] < min_removed) min_removed = assump_Cs[j];
                } else { 
                    other_conflict = true;
                    if (assump_Cs[j] < min_bound) min_bound = assump_Cs[j];
                }
                assump_Cs[j] = -assump_Cs[j]; removed++;
            }
        }
        if (other_conflict && min_removed != Int_MAX && opt_minimization != 1) min_removed = 0;
        vec<int> modified_saved_constrs;
        if (removed > 0) {
            int j = 0;
            for (int i = 0; i < assump_ps.size(); i++) {
                if (assump_Cs[i] < 0) {
                    Minisat::Lit p = assump_ps[i];
                    if (opt_minimization == 1 && p > max_assump) { // && assump_Cs[i] == -min_removed) {
                        int k = assump_map.at(toInt(p));
                        if (k >= 0 && k < saved_constrs.size() &&  saved_constrs[k] != NULL && saved_constrs[k]->lit == p) {
                            if (saved_constrs[k]->lo != Int_MIN && saved_constrs[k]->lo > 1 || 
                                    saved_constrs[k]->hi != Int_MAX && saved_constrs[k]->hi < saved_constrs[k]->size - 1) {
                                if (saved_constrs[k]->lo != Int_MIN) --saved_constrs[k]->lo; else ++saved_constrs[k]->hi;
                                constrs.push(saved_constrs[k]); 
                                constrs.last()->lit = lit_Undef;
                                modified_saved_constrs.push(k);
                            } else { saved_constrs[k]->~Linear(); saved_constrs[k] = NULL; }
                            assump_map.set(toInt(p), -1);
                        }
                    }
                    if (assump_Cs[i] == -min_removed || opt_minimization != 1) continue;
                    assump_Cs[i] = -min_removed - assump_Cs[i];
                    if (opt_minimization == 1 &&  assump_Cs[i] < max_assump_Cs ) {
                        delayed_assump.push(Pair_new(assump_Cs[i], assump_ps[i]));
                        delayed_assump_sum += assump_Cs[i];
                        continue;
                    }
                }
                if (j < i) assump_ps[j] = assump_ps[i], assump_Cs[j] = assump_Cs[i];
                j++;
            }
            if ((removed = assump_ps.size() - j) > 0)
                assump_ps.shrink(removed), assump_Cs.shrink(removed);
            if (min_bound == Int_MAX || min_bound < LB_goalvalue) min_bound = LB_goalvalue + 1;
            LB_goalvalue = (min_removed == 0 ? next_sum(LB_goalvalue - fixed_goalval - harden_goalval, goal_Cs) + fixed_goalval + harden_goalval: 
                            min_removed == Int_MAX ? min_bound : LB_goalvalue + min_removed);
        } else if (opt_minimization == 1) LB_goalvalue = next_sum(LB_goalvalue - fixed_goalval - harden_goalval, goal_Cs) + fixed_goalval + harden_goalval; 
        else LB_goalvalue = try_lessthan;

        if (LB_goalvalue == best_goalvalue && opt_minimization != 1) break;

        Int goal_diff = harden_goalval+fixed_goalval;
        if (opt_minimization == 1) {
            assump_lit = lit_Undef;
            try_lessthan = goal_diff + 2;
	} else if (opt_minimization == 0 || best_goalvalue == Int_MAX || best_goalvalue - LB_goalvalue < opt_seq_thres) {
            assump_lit = (assump_ps.size() == 0 ? lit_Undef : mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true));
	    try_lessthan = (best_goalvalue != Int_MAX ? best_goalvalue : UB_goalvalue+1);
	} else {
            assump_lit = assump_lit == lit_Undef || !use_base_assump ?
                mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars)) : assump_lit;
	    try_lessthan = (LB_goalvalue*(100-opt_bin_percent) + best_goalvalue*(opt_bin_percent))/100;
	}
        if (!addConstr(goal_ps, goal_Cs, try_lessthan - goal_diff, -2, assump_lit))
            break; // unsat
        if (constrs.size() > 0 && (opt_minimization != 1 || !opt_delay_init_constraints)) {
            convertPbs(false);
            if (opt_minimization == 1) {
                if (constrs.size() == modified_saved_constrs.size() + 1) assump_lit = constrs.last()->lit;
                for (int i = 0, j = 0; i < modified_saved_constrs.size(); i++) {
                    int k = modified_saved_constrs[i];
                    Lit newp = constrs[j++]->lit;
                    sat_solver.setFrozen(var(newp),true);
                    sat_solver.addClause(~saved_constrs[k]->lit, newp);
                    saved_constrs[k]->lit = newp;
                    assump_ps.push(newp); assump_Cs.push(saved_constrs_Cs[k]);
                    if (saved_constrs[k]->lo > 1 || saved_constrs[k]->hi < saved_constrs[k]->size - 1)
                        assump_map.set(toInt(newp), k);
                }
                modified_saved_constrs.clear();
            }
        }
        bool use_delay = enable_dynamic_delay && constrs.size() && constrs.last()->size >= dynamic_delay_core_threshoad;
        if (!use_delay && assump_lit != lit_Undef && !use_base_assump) {
            sat_solver.setFrozen(var(assump_lit),true);
            assump_ps.push(assump_lit); assump_Cs.push(opt_minimization == 2 ? try_lessthan : 
                                                       min_removed != Int_MAX && min_removed != 0 ? min_removed : 1);
        }
        if (opt_minimization == 1) {
            if (constrs.size() > 0 && constrs.last()->lit == assump_lit) {
                if(use_delay)
                {
                    if (constrs.last()->lit != assump_lit) assump_lit = assump_ps.last() = constrs.last()->lit;
                    delayed_assump_sum += min_removed;
                    delayed_assump.push(Pair_new(min_removed, assump_lit), constrs.last()->size);
                    saved_constrs.push(constrs.last()), assump_map.set(toInt(assump_lit),saved_constrs.size() - 1);
                    saved_constrs_Cs.push(min_removed);
                }
                else {
                Minisat::vec<Lit> new_assump; 
                optimize_last_constraint(constrs, assump_ps, new_assump);
                if (new_assump.size() > 0) {
                    delayed_assump_sum += Int(new_assump.size()) * assump_Cs.last();
                    for (int i=0; i < new_assump.size(); i++) 
                        delayed_assump.push(Pair_new(assump_Cs.last(), new_assump[i]));
                }
                if (constrs.last()->lit != assump_lit) assump_lit = assump_ps.last() = constrs.last()->lit;
                saved_constrs.push(constrs.last()), assump_map.set(toInt(assump_lit),saved_constrs.size() - 1);
                saved_constrs_Cs.push(assump_Cs.last());
                }
            } else if (goal_ps.size() > 1) {
                saved_constrs.push(new (mem.alloc(sizeof(Linear) + goal_ps.size()*(sizeof(Lit) + sizeof(Int))))
                        Linear(goal_ps, goal_Cs, Int_MIN, 1, assump_lit));
                assump_map.set(toInt(assump_lit),saved_constrs.size() - 1);
                saved_constrs_Cs.push(assump_Cs.last());
            }
            if (!opt_delay_init_constraints) {
                int j = 0;
                for (int i = 0; i < saved_constrs.size(); i++)
                    if (saved_constrs[i] != NULL) {
                        if (saved_constrs[i]->lo == 1 && saved_constrs[i]->hi == Int_MAX || 
                                saved_constrs[i]->hi == saved_constrs[i]->size - 1 && saved_constrs[i]->lo == Int_MIN ) {
                            saved_constrs[i]->~Linear();
                            saved_constrs[i] = NULL;
                        } else {
                            if (j < i) {
                                saved_constrs[j] = saved_constrs[i],  saved_constrs[i] = NULL, saved_constrs_Cs[j] = saved_constrs_Cs[i];
                                if (saved_constrs[j]->lit != lit_Undef) assump_map.set(toInt(saved_constrs[j]->lit), j); 
                            }
                            j++;
                        }
                    }
                if (j < saved_constrs.size()) 
                    saved_constrs.shrink(saved_constrs.size() - j), saved_constrs_Cs.shrink(saved_constrs_Cs.size() - j);
                constrs.clear();
            }
        }
        }
        if (weighted_instance && sat && sat_solver.conflicts > 10000)
            harden_soft_cls(assump_ps, assump_Cs);
        if (opt_minimization >= 1 && opt_verbosity >= 2) {
            char *t; reportf("Lower bound  = %s, assump. size = %d, stratif. level = %d (cls: %d, wght: %s)\n", t=toString(LB_goalvalue * goal_gcd), 
                    assump_ps.size(), sorted_assump_Cs.size(), top_for_strat, toString(sorted_assump_Cs.size() > 0 ? sorted_assump_Cs.last() : 0)); xfree(t); }
        if (opt_minimization == 2 && opt_verbosity == 1 && use_base_assump) {
            char *t; reportf("Lower bound  = %s\n", t=toString(LB_goalvalue * goal_gcd)); xfree(t); }
        if (opt_minimization == 1 && opt_to_bin_search && LB_goalvalue + 5 < UB_goalvalue &&
                cpuTime() >= opt_unsat_cpu && sat_solver.conflicts > opt_unsat_cpu * 100) {
            int cnt = 0;
            for (int j = 0, i = 0; i < psCs.size(); i++) {
                const Int &w = soft_cls[psCs[i].snd].fst;
                if (j == assump_ps.size() || psCs[i].fst < assump_ps[j] || psCs[i].fst == assump_ps[j] && w > assump_Cs[j])
                    if (++cnt >= 50000) { opt_to_bin_search = false; break; }
                if (j < assump_ps.size() && psCs[i].fst == assump_ps[j]) j++;
            }
            if (opt_to_bin_search) {
                for (int i = assump_ps.size() - 1; i >= 0 && assump_ps[i] > max_assump; i--)
                    assump_ps.pop(), assump_Cs.pop();
                goal_ps.clear(); goal_Cs.clear();
                bool clear_assump = (cnt * 3 >= assump_ps.size()); use_base_assump = clear_assump;
                int k = 0;
                for (int j = 0, i = 0; i < psCs.size(); i++) {
                    const Int &w = soft_cls[psCs[i].snd].fst;
                    bool in_harden = harden_lits.has(psCs[i].fst);
                    if ((j == assump_ps.size() || psCs[i].fst < assump_ps[j] || 
                            psCs[i].fst == assump_ps[j] && (clear_assump || w > assump_Cs[j] || in_harden)) &&
                        (!in_harden || harden_lits.at(psCs[i].fst) < w))
                            goal_ps.push(~psCs[i].fst), goal_Cs.push(in_harden ? w - harden_lits.at(psCs[i].fst) : w);
                    if (j < assump_ps.size() && psCs[i].fst == assump_ps[j]) {
                        if (!clear_assump && w == assump_Cs[j] && !in_harden) { 
                            if (k < j) assump_ps[k] = assump_ps[j], assump_Cs[k] = assump_Cs[j];
                            k++;
                        }
                        j++;
                    }
                }      
                if (k < assump_ps.size()) assump_ps.shrink(assump_ps.size() - k), assump_Cs.shrink(assump_Cs.size() - k);
                for (int i = 0; i < top_for_strat; i++) { 
                    if (soft_cls[i].snd->size() > 1) sat_solver.addClause(*soft_cls[i].snd);
                }
                for (int i = 0; i < am1_rels.size(); i++) goal_ps.push(~am1_rels[i].fst), goal_Cs.push(am1_rels[i].snd);
                top_for_strat = 0; sorted_assump_Cs.clear(); am1_rels.clear(); harden_lits.clear();
                delayed_assump.clear(); delayed_assump_sum = 0;
                if (opt_verbosity >= 1) {
                    reportf("Switching to binary search ... (after %g s and %d conflicts) with %d goal literals and %d assumptions\n", 
                            cpuTime(), sat_solver.conflicts, goal_ps.size(), assump_ps.size());
                }
                opt_minimization = 2;
                if (sat) {
                    try_lessthan = best_goalvalue; 
                    assump_lit = (assump_ps.size() == 0 && !use_base_assump ? lit_Undef : 
                                                          mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true));
                    if (assump_lit != lit_Undef && !use_base_assump) assump_ps.push(assump_lit), assump_Cs.push(try_lessthan);
                    if (!addConstr(goal_ps, goal_Cs, try_lessthan - fixed_goalval - harden_goalval, -2, assump_lit))
                        break; // unsat
                    if (constrs.size() > 0) convertPbs(false);
                }
            }
        }
      }         
    } // END OF LOOP

    if (status == l_False && opt_output_top > 0) printf("v\n");
    if (goal_gcd != 1) {
        if (best_goalvalue != Int_MAX) best_goalvalue *= goal_gcd;
        if (LB_goalvalue   != Int_MIN) LB_goalvalue *= goal_gcd;
        if (UB_goalvalue   != Int_MAX) UB_goalvalue *= goal_gcd;
    }
    if (opt_verbosity >= 1 && opt_output_top < 0){
        if      (!sat)
            reportf(asynch_interrupt ? "\bUNKNOWN\b\n" : "\bUNSATISFIABLE\b\n");
        else if (soft_cls.size() == 0 && best_goalvalue == INT_MAX)
            reportf("\bSATISFIABLE: No goal function specified.\b\n");
        else if (cmd == sc_FirstSolution){
            char* tmp = toString(best_goalvalue);
            reportf("\bFirst solution found: %s\b\n", tmp);
            xfree(tmp);
        }else if (asynch_interrupt){
            extern bool opt_use_maxpre;
            char* tmp = toString(best_goalvalue);
            if (!opt_use_maxpre) reportf("\bSATISFIABLE: Best solution found: %s\b\n", tmp);
            xfree(tmp);
       }else{
            char* tmp = toString(best_goalvalue);
            reportf("\bOptimal solution: %s\b\n", tmp);
            xfree(tmp);
        }
    }
}

void set_difference(vec<Lit>& set1, const vec<Lit>& set2)
{
    int j =0, k = 0;
    for (int i = 0; i < set1.size(); i++) {
        while (k < set2.size() && set2[k] < set1[i]) k++;
        if (k < set2.size() && set1[i] == set2[k]) { k++; continue; }
        if (j < i) set1[j] = set1[i];
        j++;
    }
    if (j < set1.size()) set1.shrink(set1.size() - j);
}

struct mapLT { Map<Lit, vec<Lit>* >&c; bool operator()(Lit p, Lit q) { return c.at(p)->size() < c.at(q)->size(); }};

void MsSolver::preprocess_soft_cls(Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs, const Lit max_assump, const Int& max_assump_Cs, 
                                              IntLitQueue& delayed_assump, Int& delayed_assump_sum)
{
    Map<Lit, vec<Lit>* > conns;
    vec<Lit> conns_lit;
    vec<Lit> confl;
    vec<Lit> lits;
    for (int i = 0; i < assump_ps.size() && assump_ps[i] <= max_assump; i++) {
        Minisat::vec<Lit> props;
        Lit assump = assump_ps[i];
        if (sat_solver.prop_check(assump, props))
            for (int l, j = 0; j < props.size(); j++) {
                if ((l = bin_search(assump_ps,  ~props[j])) >= 0 && assump_ps[l] <= max_assump) {
                    if (!conns.has(assump)) conns.set(assump,new vec<Lit>());
                    conns.ref(assump)->push(~props[j]);
                    if (!conns.has(~props[j])) conns.set(~props[j], new vec<Lit>());
                    conns.ref(~props[j])->push(assump);
                }
            }  
        else confl.push(assump);
    }
    conns.domain(conns_lit);
    if (confl.size() > 0) {
        for (int i = 0; i < conns_lit.size(); i++) {
            if (bin_search(confl, conns_lit[i]) >= 0) {
                delete conns.ref(conns_lit[i]);
                conns.exclude(conns_lit[i]);
            } else {
                vec<Lit>& dep_lit = *conns.ref(conns_lit[i]);
                sortUnique(dep_lit);
                set_difference(dep_lit, confl);
                if (dep_lit.size() == 0) { delete conns.ref(conns_lit[i]); conns.exclude(conns_lit[i]); }
                else lits.push(conns_lit[i]);
            }
        }
        conns_lit.clear(); conns.domain(conns_lit);
        for (int l, i = 0; i < confl.size(); i++) {
            Lit p = confl[i];
            if ((l = bin_search(assump_ps, p)) >= 0 && assump_ps[l] <= max_assump) {
                if (!harden_lits.has(p)) harden_lits.set(p, assump_Cs[l]); else harden_lits.ref(p) += assump_Cs[l];
                harden_goalval += assump_Cs[l];
                addUnit(~p); LB_goalvalue += assump_Cs[l]; assump_Cs[l] = -assump_Cs[l];
            }
        }
        if (opt_verbosity >= 2) reportf("Found %d Unit cores\n", confl.size());
    } else
        for (int i = 0; i < conns_lit.size(); i++) { 
            lits.push(conns_lit[i]); 
            sortUnique(*conns.ref(conns_lit[i])); 
        }
    sort(lits);
    mapLT cmp {conns};
    int am1_cnt = 0, am1_len_sum = 0;
    while (lits.size() > 0) {
        vec<Lit> am1;
        Lit minl = lits[0];
        for (int new_sz,  sz = conns.at(minl)->size(), i = 1; i < lits.size(); i++)
            if ((new_sz = conns.at(lits[i])->size()) < sz) minl = lits[i], sz = new_sz;
        am1.push(minl);
        vec<Lit>& dep_minl = *conns.ref(minl);
        sort(dep_minl, cmp);
        for (int sz = dep_minl.size(), i = 0; i < sz; i++) {
            Lit l = dep_minl[i];
            if (bin_search(lits, l) >= 0) {
                int i;
                const vec<Lit>& dep_l = *conns.at(l);
                for (i = 1; i < am1.size() && bin_search(dep_l, am1[i]) >= 0; ++i);
                if (i == am1.size()) am1.push(l);
            }
        }
        sort(dep_minl);
        sort(am1);
        set_difference(lits, am1);
        for (int i = 0; i < conns_lit.size(); i++)  set_difference(*conns.ref(conns_lit[i]), am1);
        if (am1.size() > 1) {
            Minisat::vec<Lit> cls;
            vec<int> ind;
            Int min_Cs = Int_MAX;
            for (int l, i = 0; i < am1.size(); i++)
                if ((l = bin_search(assump_ps, am1[i])) >= 0 && assump_Cs[l] > 0) {
                    ind.push(l);
                    if (assump_Cs[l] < min_Cs) min_Cs = assump_Cs[l];
                }
                else reportf("am1: %d %d %d %s\n", i, am1.size(), toInt(am1[0]), toInt(am1[i]), (l>=0 && l <assump_Cs.size()?toString(assump_Cs[l]):"???"));
            if (ind.size() < 2) continue;
            for (int i = 0; i < ind.size(); i++) {
                if (assump_Cs[ind[i]] == min_Cs) cls.push(assump_ps[ind[i]]), assump_Cs[ind[i]] = -assump_Cs[ind[i]];
                else {
                    cls.push(assump_ps[ind[i]]); //~r);
                    assump_Cs[ind[i]] -= min_Cs;
                    if (assump_Cs[i] < max_assump_Cs) {
                        delayed_assump.push(Pair_new(assump_Cs[ind[i]], assump_ps[ind[i]]));
                        delayed_assump_sum += assump_Cs[ind[i]];
                        assump_Cs[ind[i]] = - assump_Cs[ind[i]];
                    }
                }
                if (!harden_lits.has(assump_ps[ind[i]])) harden_lits.set(assump_ps[ind[i]], min_Cs);
                else harden_lits.ref(assump_ps[ind[i]]) += min_Cs;
            }
            Lit r = mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true);
            sat_solver.setFrozen(var(r), true);
            cls.push(~r);
            std::vector<Lit> mytemcls;
            for (int i = 0; i < cls.size(); ++i)
            {
                mytemcls.push_back((cls[i]));
            }
            assump_ps.push(r);
            assump_Cs.push(min_Cs);
            am1_rels.push(Pair_new(r, min_Cs));
            am1_cls.push_back(mytemcls);
            sat_solver.addClause(cls);
            if (ind.size() > 2)
                min_Cs = Int(ind.size() - 1) * min_Cs;
            am1_cnt++;
            am1_len_sum += am1.size();
            LB_goalvalue += min_Cs;
            harden_goalval += min_Cs;
        }
    }
    if (am1_cnt > 0 || confl.size() > 0) clear_assumptions(assump_ps, assump_Cs);
    if (opt_verbosity >= 2 && am1_cnt > 0) 
        reportf("Found %d AtMostOne cores of avg size: %.2f\n", am1_cnt, (double)am1_len_sum/am1_cnt);
}

