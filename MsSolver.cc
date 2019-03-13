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
#include "minisat/utils/System.h"
#include "Sort.h"
#include "Debug.h"

static Int gcd(Int small, Int big) {
    return (small == 0) ? big: gcd(big % small, small); }
        
static PbSolver *pb_solver;
static
void SIGINT_interrupt(int /*signum*/) { pb_solver->sat_solver.interrupt(); pb_solver->asynch_interrupt=true; }

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


static
Int evalGoal(Linear& goal, vec<bool>& model, Map<int, Minisat::vec<Lit>*> *soft_cls_map = NULL)
{
    Int sum = 0;
    bool sat = false;
    for (int i = 0; i < goal.size; i++) {
        assert(var(goal[i]) < model.size());
        if ((( sign(goal[i]) && !model[var(goal[i])]) || (!sign(goal[i]) &&  model[var(goal[i])])) 
            && (!soft_cls_map || !(sat = satisfied_soft_cls(soft_cls_map->at(toInt(goal[i])), model))))
            sum += goal(i);
        if (sat) { sat = false; model[var(goal[i])] = ~model[var(goal[i])]; }
    }
    return sum;
}

static
void core_minimization(SimpSolver &sat_solver, Minisat::vec<Lit> &mus)
{
    int last_size = sat_solver.conflict.size();

    sat_solver.setConfBudget(1000);
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

static
Int evalPsCs(vec<Lit>& ps, vec<Int>&Cs, vec<bool>& model)
{
    Int sum = 0;
    assert(ps.size() == Cs.size());
    for (int i = 0; i < ps.size(); i++){
        if (( sign(ps[i]) && model[var(ps[i])] == false)
        ||  (!sign(ps[i]) && model[var(ps[i])] == true )
        )
            sum += Cs[i];
    }
    return sum;
}

/*static
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

static void opt_stratification(vec<Int>& sorted_assump_Cs, vec<Pair<Int, bool> >& sum_sorted_soft_cls)
{
    assert(sorted_assump_Cs.size() == sum_sorted_soft_cls.size());

    int m = max(1, sum_sorted_soft_cls.size() - 10);
    if (m < 10) m = 1;
    for (int i = sum_sorted_soft_cls.size() - 1; i >= m; i--)
        if (sorted_assump_Cs[i] > sorted_assump_Cs[i-1] + 1 || 
                i < sum_sorted_soft_cls.size() - 1 && !sum_sorted_soft_cls[i + 1].snd) 
            sum_sorted_soft_cls[i].snd = true;
    if (m == 1) return;
    vec<Pair<Int, int> > gaps;
    for (int i = 0; i < m; i++) gaps.push(Pair_new(sorted_assump_Cs[i+1] - sorted_assump_Cs[i], i + 1));
    sort(gaps);
    for (int i = gaps.size() - 1, j = 0; j < 10; j++, i--) sum_sorted_soft_cls[gaps[i].snd].snd = true;
}

template <class T> struct LT {bool operator()(T x, T y) { return x.snd->last() < y.snd->last(); }};

static Int do_stratification(SimpSolver& S, vec<Int>& sorted_assump_Cs, vec<Pair<Int, Minisat::vec<Lit>* > >& soft_cls, 
                                            Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs)
{
    Int  max_assump_Cs;
    //do { max_assump_Cs = sorted_assump_Cs.last(); sorted_assump_Cs.pop(); 
    //} while (sorted_assump_Cs.size() > 0 && !sum_sorted_soft_cls[sorted_assump_Cs.size()].snd);
    max_assump_Cs = sorted_assump_Cs.last(); sorted_assump_Cs.pop();
    if (sorted_assump_Cs.size() > 0 && sorted_assump_Cs.last() == max_assump_Cs - 1) 
        max_assump_Cs = sorted_assump_Cs.last(), sorted_assump_Cs.pop(); 
    int start = soft_cls.size() - 1;
    while (start >= 0 && soft_cls[start].fst >= max_assump_Cs) start--;
    start++;
    if (start < soft_cls.size()) {
        int sz = soft_cls.size() - start, to = 0, fr = sz;
        sort(&soft_cls[start], sz, LT<Pair<Int, Minisat::vec<Lit>*> >());
        assump_ps.growTo(assump_ps.size() + sz); assump_Cs.growTo(assump_Cs.size() + sz);
        for (int i = assump_ps.size() - 1; i >= sz; i--)
            assump_ps[i] = assump_ps[i-sz], assump_Cs[i] = assump_Cs[i-sz];
        for (int i = start; i < soft_cls.size(); i++) {
            Lit p = ~soft_cls[i].snd->last();
            if (soft_cls[i].snd->size() > 1) S.addClause(*soft_cls[i].snd); else p = ~p;
            while (fr < assump_ps.size() && assump_ps[fr] <= p)
                assump_ps[to] = assump_ps[fr], assump_Cs[to++] = assump_Cs[fr++];
            assump_ps[to] = p; assump_Cs[to++] = soft_cls[i].fst;
        }
        soft_cls.shrink(sz);
    }
    return max_assump_Cs;
}

static void harden_soft_cls(SimpSolver& sat_solver, Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs, vec<Pair<Int, Lit> >& Csps, 
                                                       const Int& LB_goalvalue, const Int& UB_goalvalue)
{
    int cnt_unit = 0, cnt_assump = 0, sz = 0;
    Int bound = UB_goalvalue - LB_goalvalue;
    for (int i = Csps.size() - 1; i >= 0 && Csps[i].fst > bound; i--) { // hardening soft clauses with weights > the current goal interval length 
        if (Csps[i].fst > UB_goalvalue) sz++;
        Lit p = Csps[i].snd;
        int j = std::lower_bound(&assump_ps[0], &assump_ps[0] + assump_ps.size(), p) - &assump_ps[0];
        if (j >= 0 && j < assump_ps.size() && p == assump_ps[j] && assump_Cs[j] > bound) {
            assump_Cs[j] = -assump_Cs[j]; // mark a corresponding assumption to be deleted
            cnt_assump++; cnt_unit++; sat_solver.addClause(p);
        } else if (Csps[i].fst > UB_goalvalue) cnt_unit++, sat_solver.addClause(p);
    }
    if (opt_verbosity >= 2 && cnt_unit > 0) reportf("Hardened %d soft clauses\n", cnt_unit);
    if (sz > 0 ) Csps.shrink(sz);
    if (cnt_assump > 0) clear_assumptions(assump_ps, assump_Cs);
}
static inline int log2(int n) { int i=0; while (n>>=1) i++; return i; }

void PbSolver::maxsat_solve(solve_Command cmd)
{
    if (!okay()) {
        if (opt_verbosity >= 1) sat_solver.printVarsCls();
        return;
    }
#if defined(GLUCOSE3) || defined(GLUCOSE4)    
    if (opt_verbosity >= 1) sat_solver.verbEveryConflicts = 100000;
    sat_solver.setIncrementalMode();
#endif
    if (goal == NULL) { opt_maxsat_msu = false; solve(cmd); return; }
    // Convert constraints:
    pb_n_vars = nVars();
    pb_n_constrs = nClauses();

    // Freeze goal function variables (for SatELite):
    for (int i = 0; i < goal->size; i++)
        sat_solver.setFrozen(var((*goal)[i]), true);
    sat_solver.verbosity = opt_verbosity - 1;

    Int goal_gcd = (*goal)(0);
    for (int i = 1; i < goal->size && goal_gcd != 1; ++i) goal_gcd = gcd(goal_gcd, (*goal)(i));
    if (goal_gcd != 1) {
        if (LB_goalvalue != Int_MIN) LB_goalvalue /= goal_gcd;
        if (UB_goalvalue != Int_MAX) UB_goalvalue /= goal_gcd;
    }

    assert(best_goalvalue == Int_MAX);

    if (opt_polarity_sug != 0){
        for (int i = 0; i < goal->size; i++){
            bool dir = (*goal)(i)*opt_polarity_sug > 0 ? !sign((*goal)[i]) : sign((*goal)[i]);
            sat_solver.setPolarity(var((*goal)[i]), LBOOL(dir));
        }
    }

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
    signal(SIGXCPU,SIGINT_interrupt);

    Map<int,int> assump_map(-1);
    Map<int, Minisat::vec<Lit>*> soft_cls_map(NULL);
    vec<Linear*> saved_constrs;
    vec<Lit> goal_ps;
    Minisat::vec<Lit> assump_ps;
    vec<Int> goal_Cs, assump_Cs, sorted_assump_Cs, saved_constrs_Cs;
    vec<Pair<Int, bool> > sum_sorted_soft_cls;
    bool    sat = false, weighted_instance = true;
    Lit inequality = lit_Undef, max_assump = lit_Undef;
    Int     try_lessthan = opt_goal, max_assump_Cs = Int_MIN;
    int     n_solutions = 0;    // (only for AllSolutions mode)
    vec<Pair<Lit,Int> > psCs;
    vec<Pair<Int,Lit> > Csps;
    vec<bool> multi_level_opt;
    bool opt_delay_init_constraints = false, 
         opt_core_minimization = (nClauses() > 0 || soft_cls.size() < 100000);

    assert(goal->size == soft_cls.size());
    for (int i = 0; i < goal->size; i++)
        soft_cls_map.set(toInt((*goal)[i]), soft_cls[i].snd);

    Int LB_goalval = 0, UB_goalval = 0, fixed_goalval = 0;    
    sort(&soft_cls[0], soft_cls.size(), LT<Pair<Int, Minisat::vec<Lit>*> >());
    int j = 0; Lit pj;
    for (int i = 0; i < soft_cls.size(); ++i) {
        soft_cls[i].fst /= goal_gcd;
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
            soft_cls[j-1].fst -= soft_cls[i].fst;
            if (soft_cls[j-1].fst < 0) soft_cls[j-1].fst = -soft_cls[j-1].fst, soft_cls[j-1].snd->last() = pj, pj = ~pj; 
        } else { 
            if (j < i) soft_cls[j] = soft_cls[i];
            pj = p; j++;
        }
    }
    if (j < soft_cls.size()) soft_cls.shrink(soft_cls.size() - j);
    for (int i = 0; i < soft_cls.size(); i++) {
        Lit p = soft_cls[i].snd->last();
        if (soft_cls[i].snd->size() == 1) p = ~p;
        UB_goalval += soft_cls[i].fst;
        psCs.push(Pair_new(~p, soft_cls[i].fst));
    }
    LB_goalval += fixed_goalval, UB_goalval += fixed_goalval;
    sort(soft_cls);
    weighted_instance = (soft_cls[0].fst != soft_cls.last().fst);
    for (int i = 0; i < soft_cls.size(); i++) {
        Lit p = soft_cls[i].snd->last();
        Csps.push(Pair_new(soft_cls[i].fst, (soft_cls[i].snd->size() == 1? p : ~p)));
        if (weighted_instance) sorted_assump_Cs.push(soft_cls[i].fst);
    }
    if (weighted_instance) sortUnique(sorted_assump_Cs);
    if (UB_goalvalue == Int_MAX) {
        UB_goalvalue = UB_goalval;
    } else {
        for (int i = 0; i < psCs.size(); i++)
            goal_ps.push(~psCs[i].fst), goal_Cs.push(psCs[i].snd);
        try_lessthan = ++UB_goalvalue;
        if (goal_ps.size() > 0) {
            addConstr(goal_ps, goal_Cs, try_lessthan - fixed_goalval, -2, inequality);
            convertPbs(false);
        }
    }
    if (LB_goalvalue < LB_goalval) LB_goalvalue = LB_goalval;
    if (opt_minimization != 1 || sorted_assump_Cs.size() == 0) {
        for (int i = 0; i < psCs.size(); i++)
            assump_ps.push(psCs[i].fst), assump_Cs.push(psCs[i].snd);
        for (int i = 0; i < soft_cls.size(); i++) { 
            if (soft_cls[i].snd->size() > 1) sat_solver.addClause(*soft_cls[i].snd);
        }
        soft_cls.clear();
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
        if (ml_opt >= 2 || !opt_to_bin_search && ml_opt >= 1) opt_lexicographic = true;
        if (opt_verbosity >= 1 && ml_opt > 0) 
            reportf("Boolean lexicographic optimization can be done in %d point(s).%s\n", 
                    ml_opt, (opt_lexicographic ? "" : " Try -lex-opt option."));
        max_assump_Cs = do_stratification(sat_solver, sorted_assump_Cs, soft_cls, assump_ps, assump_Cs);
    }
    if (psCs.size() > 0) max_assump = psCs.last().fst;
    if (opt_maxsat_prepr) preprocess_soft_cls(sat_solver, assump_ps, assump_Cs, LB_goalvalue, max_assump);
    if (opt_verbosity >= 1)
        sat_solver.printVarsCls(goal_ps.size() > 0, &soft_cls);
    while (1) {
      if (asynch_interrupt) { reportf("Interrupted ***\n"); break; }
      if (sat_solver.solve(assump_ps)) { // SAT returned
        if (opt_minimization == 1 && opt_delay_init_constraints) {
            opt_delay_init_constraints = false;
            convertPbs(false);
            constrs.clear();
            continue;
        }
        Int lastCs = 1;
        if(opt_minimization != 1 && assump_ps.size() == 1 && assump_ps.last() == inequality) {
          addUnit(inequality);
          lastCs = assump_Cs.last();
          assump_ps.pop(); assump_Cs.pop(); inequality = lit_Undef;
        }
        sat = true;

        if (cmd == sc_AllSolutions){
            Minisat::vec<Lit>    ban;
            n_solutions++;
            reportf("MODEL# %d:", n_solutions);
            for (Var x = 0; x < pb_n_vars; x++){
                assert(sat_solver.model[x] != l_Undef);
                ban.push(mkLit(x, sat_solver.model[x] == l_True));
                if (index2name[x][0] != '#')
                    reportf(" %s%s", (sat_solver.model[x] == l_False)?"-":"", index2name[x]);
            }
            reportf("\n");
            sat_solver.addClause_(ban);
        }else{
            vec<bool> model;
            for (Var x = 0; x < pb_n_vars; x++)
                assert(sat_solver.model[x] != l_Undef),
                model.push(sat_solver.model[x] == l_True);
            for (int i = 0; i < soft_cls.size(); i++)
                if (soft_cls[i].snd->size() > 1) {
                    model[var(soft_cls[i].snd->last())] = true;
                    for (int j = soft_cls[i].snd->size() - 2; j >= 0; j--) {
                        Lit p = (*soft_cls[i].snd)[j];
                        if (( sign(p) && !model[var(p)]) || (!sign(p) && model[var(p)])) {
                                model[var(soft_cls[i].snd->last())] = false;
                                break;
                        }
                    }
                }
            for (int i = 0; i < soft_cls.size(); i++)
                if (soft_cls[i].snd->size() > 1)
                    model[var(soft_cls[i].snd->last())] = true;
            Int goalvalue = evalGoal(*goal, model, &soft_cls_map) / goal_gcd;
            if (goalvalue < best_goalvalue) {
                best_goalvalue = goalvalue;
                model.moveTo(best_model);
                char* tmp = toString(best_goalvalue * goal_gcd);
                if (opt_satlive || opt_verbosity == 0)
                    printf("o %s\n", tmp), fflush(stdout);
                else reportf("\bFound solution: %s\b\n", tmp);
                xfree(tmp);
            } else model.clear(); 
            Int goal_diff = best_goalvalue - evalPsCs(goal_ps, goal_Cs, best_model);
            if (best_goalvalue < UB_goalvalue) UB_goalvalue = best_goalvalue;

            if (cmd == sc_FirstSolution || (opt_minimization == 1 || UB_goalvalue == LB_goalvalue) && sorted_assump_Cs.size() == 0) break;
            if (opt_minimization == 1) {
                assert(sorted_assump_Cs.size() > 0); 
                if (opt_lexicographic && multi_level_opt[sorted_assump_Cs.size()]) {
                    Int bound = sum_sorted_soft_cls[sorted_assump_Cs.size()].fst;
                    int cnt_assump = 0;
                    for (int i = 0; i < assump_ps.size() && assump_ps[i] <= max_assump; i++)
                        if (assump_Cs[i] > bound)
                            addUnit(assump_ps[i]), assump_Cs[i] = -assump_Cs[i], cnt_assump++;
                    if (cnt_assump > 0) clear_assumptions(assump_ps, assump_Cs);
                    if (opt_verbosity > 0) reportf("Boolean lexicographic optimization - done.\n");
                }
                int old_sz = soft_cls.size();
                max_assump_Cs = do_stratification(sat_solver, sorted_assump_Cs, soft_cls, assump_ps, assump_Cs);
                harden_soft_cls(sat_solver, assump_ps, assump_Cs, Csps, LB_goalvalue, UB_goalvalue);
                if (soft_cls.size() < old_sz) {
                    try_lessthan = best_goalvalue;
                    if (opt_maxsat_prepr) 
                        preprocess_soft_cls(sat_solver, assump_ps, assump_Cs, LB_goalvalue, max_assump);
                }
                continue;
            } else harden_soft_cls(sat_solver, assump_ps, assump_Cs, Csps, LB_goalvalue, UB_goalvalue);
            if (opt_minimization == 0 || best_goalvalue - LB_goalvalue < opt_seq_thres) {
                inequality = (assump_ps.size() == 0 ? lit_Undef : mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true));
                try_lessthan = best_goalvalue;
            } else {
                inequality = mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true);
                try_lessthan = (LB_goalvalue*(100-opt_bin_percent) + best_goalvalue*(opt_bin_percent))/100;
            }
            if (!addConstr(goal_ps, goal_Cs, try_lessthan - goal_diff, -2, inequality))
                break; // unsat
            if (inequality != lit_Undef) {
                sat_solver.setFrozen(var(inequality),true);
                assump_ps.push(inequality), assump_Cs.push(opt_minimization == 2 ? try_lessthan : lastCs);
            }
            convertPbs(false);
        }
      } else { // UNSAT returned
        if (assump_ps.size() == 0) break;

        Minisat::vec<Lit> core_mus;
        if (opt_core_minimization) {
            if (weighted_instance) {
                vec<Pair<Pair<Int, int>, Lit> > Cs_mus;
                for (int i = 0; i < sat_solver.conflict.size(); i++) {
                    Lit p = ~sat_solver.conflict[i];
                    int j = std::lower_bound(&assump_ps[0], &assump_ps[0] + assump_ps.size(), p) - &assump_ps[0];
                    Cs_mus.push(Pair_new(Pair_new((j>=0 && j<assump_ps.size() && p==assump_ps[j]? assump_Cs[j] : 0),i),p));
                }
                sort(Cs_mus);
                for (int i = 0; i < Cs_mus.size(); i++) core_mus.push(Cs_mus[i].snd);
            } else
                for (int i = 0; i < sat_solver.conflict.size(); i++) core_mus.push(~sat_solver.conflict[i]);
            core_minimization(sat_solver, core_mus);
        } else
            for (int i = 0; i < sat_solver.conflict.size(); i++) core_mus.push(sat_solver.conflict[i]);
        if (core_mus.size() > 0 && core_mus.size() < 6) sat_solver.addClause(core_mus);
        Int min_removed = Int_MAX, min_bound = Int_MAX;
        int removed = 0;
        bool other_conflict = false;

        if (opt_minimization == 1) { 
            goal_ps.clear(); goal_Cs.clear();
        }
        for (int i = 0; i < core_mus.size(); i++) {
            Lit p = ~core_mus[i];
            int j = std::lower_bound(&assump_ps[0], &assump_ps[0] + assump_ps.size(), p) - &assump_ps[0];
            if (j >= 0 && j < assump_ps.size() && p == assump_ps[j]) { 
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
        if (removed > 0) {
            int j = 0;
            for (int i = 0; i < assump_ps.size(); i++) {
                if (assump_Cs[i] < 0) {
                    Minisat::Lit p = assump_ps[i];
                    if (opt_minimization == 1 && p > max_assump && assump_Cs[i] == -min_removed) {
                        int k = assump_map.at(toInt(p));
                        if (k >= 0 && k < saved_constrs.size() &&  saved_constrs[k] != NULL && saved_constrs[k]->lit == p) {
                            if (saved_constrs[k]->lo > 1) {
                                Lit newp = mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true);
                                sat_solver.setFrozen(var(newp),true);
                                --saved_constrs[k]->lo; saved_constrs[k]->lit = newp;
                                assump_ps.push(newp); assump_Cs.push(saved_constrs_Cs[k]);
                                constrs.push(saved_constrs[k]);
                                sat_solver.addClause(~p, newp);
                                if (saved_constrs[k]->lo > 1) assump_map.set(toInt(newp), k);
                            } else { saved_constrs[k]->~Linear(); saved_constrs[k] = NULL; }
                            assump_map.set(toInt(p), -1);
                        }
                    }
                    if (assump_Cs[i] == -min_removed || opt_minimization != 1) continue;
                    assump_Cs[i] = -min_removed - assump_Cs[i];
                }
                if (j < i) assump_ps[j] = assump_ps[i], assump_Cs[j] = assump_Cs[i];
                j++;
            }
            if ((removed = assump_ps.size() - j) > 0)
                assump_ps.shrink(removed), assump_Cs.shrink(removed);
            if (min_bound == Int_MAX || min_bound < LB_goalvalue) min_bound = LB_goalvalue + 1;
            LB_goalvalue = (min_removed == 0 ? next_sum(LB_goalvalue, goal_Cs) : 
                            min_removed == Int_MAX ? min_bound : LB_goalvalue + min_removed);
        } else if (opt_minimization == 1) LB_goalvalue = next_sum(LB_goalvalue, goal_Cs); 
        else LB_goalvalue = try_lessthan;

        if (LB_goalvalue == best_goalvalue && opt_minimization != 1) break;

        Int goal_diff = best_goalvalue == Int_MAX || opt_minimization == 2 ? fixed_goalval : best_goalvalue - evalPsCs(goal_ps, goal_Cs, best_model);
        if (opt_minimization == 1) {
            inequality = mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true);
            try_lessthan = goal_diff + 2;
	} else if (opt_minimization == 0 || best_goalvalue == Int_MAX || best_goalvalue - LB_goalvalue < opt_seq_thres) {
            inequality = (assump_ps.size() == 0 ? lit_Undef : mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true));
	    try_lessthan = (best_goalvalue != Int_MAX ? best_goalvalue : UB_goalvalue+1);
	} else {
	    inequality = mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true);
	    try_lessthan = (LB_goalvalue*(100-opt_bin_percent) + best_goalvalue*(opt_bin_percent))/100;
	}
 
        if (!addConstr(goal_ps, goal_Cs, try_lessthan - goal_diff, -2, inequality))
            break; // unsat
        if (inequality != lit_Undef) {
            sat_solver.setFrozen(var(inequality),true);
            assump_ps.push(inequality); assump_Cs.push(opt_minimization == 2 ? try_lessthan : 
                                                       min_removed != Int_MAX && min_removed != 0 ? min_removed : 1);
        }
        if (constrs.size() > 0 && (opt_minimization != 1 || !opt_delay_init_constraints)) convertPbs(false);
        if (opt_minimization == 1) {
            if (constrs.size() > 0 && constrs.last()->lit == inequality)
                saved_constrs.push(constrs.last()), assump_map.set(toInt(inequality),saved_constrs.size() - 1),
                saved_constrs_Cs.push(assump_Cs.last());
            if (!opt_delay_init_constraints) {
                int j = 0;
                for (int i = 0; i < saved_constrs.size(); i++)
                    if (saved_constrs[i] != NULL) {
                        if (saved_constrs[i]->lo == 1 && saved_constrs[i]->hi == Int_MAX) {
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
        if (weighted_instance && sat && sat_solver.conflicts > 10000)
            harden_soft_cls(sat_solver, assump_ps, assump_Cs, Csps, LB_goalvalue, UB_goalvalue);
        if (opt_minimization >= 1 && opt_verbosity >= 2) {
            char *tmp; reportf("Lower bound  = %s\n", tmp=toString(LB_goalvalue * goal_gcd)); xfree(tmp); }
        if (opt_minimization == 1 && opt_to_bin_search && LB_goalvalue + 5 < UB_goalvalue &&
                Minisat::cpuTime() >= opt_unsat_cpu && sat_solver.conflicts > opt_unsat_cpu * 100) {
            int cnt = 0;
            for (int j = 0, i = 0; i < psCs.size(); i++) {
                if (j == assump_ps.size() || psCs[i].fst < assump_ps[j] || psCs[i].fst == assump_ps[j] && psCs[i].snd > assump_Cs[j])
                    if (++cnt >= 50000) { opt_to_bin_search = false; break; }
                if (j < assump_ps.size() && psCs[i].fst == assump_ps[j]) j++;
            }
            if (opt_to_bin_search) {
                for (int i = assump_ps.size() - 1; i >= 0 && assump_ps[i] > max_assump; i--)
                    sat_solver.addClause(~assump_ps[i]), assump_ps.pop(), assump_Cs.pop();
                goal_ps.clear(); goal_Cs.clear();
                int k = 0;
                for (int j = 0, i = 0; i < psCs.size(); i++) {
                    if (j == assump_ps.size() || psCs[i].fst < assump_ps[j] || 
                            psCs[i].fst == assump_ps[j] && psCs[i].snd > assump_Cs[j])
                        goal_ps.push(~psCs[i].fst), goal_Cs.push(psCs[i].snd);
                    if (j < assump_ps.size() && psCs[i].fst == assump_ps[j]) {
                        if (psCs[i].snd == assump_Cs[j]) { 
                            if (k < j) assump_ps[k] = assump_ps[j], assump_Cs[k] = assump_Cs[j];
                            k++;
                        }
                        j++;
                    }
                }
                if (k < assump_ps.size()) assump_ps.shrink(assump_ps.size() - k), assump_Cs.shrink(assump_Cs.size() - k);
                for (int i = 0; i < soft_cls.size(); i++) { 
                    if (soft_cls[i].snd->size() > 1) sat_solver.addClause(*soft_cls[i].snd);
                }
                soft_cls.clear();
                if (opt_verbosity >= 1) {
                    reportf("Switching to binary search ... (after %g s and %d conflicts) with %d goal literals\n", 
                            Minisat::cpuTime(), sat_solver.conflicts, cnt);
                }
                opt_minimization = 2;
                if (sat) {
                    try_lessthan = evalPsCs(goal_ps, goal_Cs, best_model); 
                    inequality = (assump_ps.size() == 0 ? lit_Undef : mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true));
                    if (inequality != lit_Undef) assump_ps.push(inequality), assump_Cs.push(try_lessthan);
                    if (!addConstr(goal_ps, goal_Cs, try_lessthan, -2, inequality)) break; // unsat
                    if (constrs.size() > 0) convertPbs(false);
                }
            }
        }
      }         
    } // END OF LOOP

    if (goal_gcd != 1) {
        if (best_goalvalue != Int_MAX) best_goalvalue *= goal_gcd;
        if (LB_goalvalue   != Int_MIN) LB_goalvalue *= goal_gcd;
        if (UB_goalvalue   != Int_MAX) UB_goalvalue *= goal_gcd;
    }
    if (opt_verbosity >= 1){
        if      (!sat)
            reportf(asynch_interrupt ? "\bUNKNOWN\b\n" : "\bUNSATISFIABLE\b\n");
        else if (goal == NULL)
            reportf("\bSATISFIABLE: No goal function specified.\b\n");
        else if (cmd == sc_FirstSolution){
            char* tmp = toString(best_goalvalue);
            reportf("\bFirst solution found: %s\b\n", tmp);
            xfree(tmp);
        }else if (asynch_interrupt){
            char* tmp = toString(best_goalvalue);
            reportf("\bSATISFIABLE: Best solution found: %s\b\n", tmp);
            xfree(tmp);
       }else{
            char* tmp = toString(best_goalvalue);
            reportf("\bOptimal solution: %s\b\n", tmp);
            xfree(tmp);
        }
    }
}

#include<vector>
#include<algorithm>

void PbSolver::preprocess_soft_cls(SimpSolver& sat_solver, Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs, Int& LB_goalvalue, const Lit max_assump)
{
    std::map<Lit,std::vector<Lit> > conns;
    std::vector<Lit> confl;
    for (int i = 0; i < assump_ps.size() && assump_ps[i] <= max_assump; i++) {
        Minisat::vec<Lit> assump, props; 
        assump.push(assump_ps[i]);
        if (sat_solver.prop_check(assump, props, 2))
            for (int j = 0; j < props.size(); j++) {
                int l = std::lower_bound(&assump_ps[0], &assump_ps[0]+assump_ps.size(),  ~props[j]) - &assump_ps[0]; 
                if (l >= 0 && l < assump_ps.size() && ~props[j] == assump_ps[l] && assump_ps[l] <= max_assump) {
                    conns[assump[0]].push_back(~props[j]);
                    conns[~props[j]].push_back(assump[0]);
                }
            }  
        else confl.push_back(assump_ps[i]);
    }
    if (confl.size() > 0) {
        for (auto it : conns)
            if (std::binary_search(confl.begin(), confl.end(), it.first))
                conns.erase(it.first);
            else {
                sort(it.second.begin(),it.second.end());
                auto lst = std::set_difference(it.second.begin(),it.second.end(),confl.begin(),confl.end(),it.second.begin());
                if (lst == it.second.begin()) conns.erase(it.first);
                else it.second.resize(lst - it.second.begin());
            }
        for (Lit p : confl) {
            int l = std::lower_bound(&assump_ps[0], &assump_ps[0]+assump_ps.size(), p) - &assump_ps[0];
            if (l >= 0 && l < assump_ps.size() && assump_ps[l] == p && assump_ps[l] <= max_assump) {
                addUnit(~p); LB_goalvalue += assump_Cs[l]; assump_Cs[l] = -assump_Cs[l];
            }
        }
        if (opt_verbosity >= 2) reportf("Found %d Unit cores\n", confl.size());
    }
    int am1_cnt = 0, am1_len_sum = 0;
    std::vector<Lit> lits;
    for (auto &l : conns) { lits.push_back(l.first); std::sort(l.second.begin(), l.second.end()); }
    while (lits.size() > 0) {
        std::vector<Lit> am1;
        am1.push_back(*std::min_element(lits.begin(), lits.end(), 
                    [&](Lit p, Lit q) { return conns[p].size() < conns[q].size(); }));
        std::sort(conns[am1[0]].begin(), conns[am1[0]].end(), 
                    [&](Lit p, Lit q) { return conns[p].size() < conns[q].size(); });
        for (Lit l : conns[am1[0]])
            if (std::binary_search(lits.begin(), lits.end(), l)) {
                unsigned i;
                for (i = 1; i < am1.size(); ++i)
                    if (std::find(conns[l].begin(), conns[l].end(),am1[i]) == conns[l].end())
                        break;
                if (i == am1.size()) am1.push_back(l);
            }
        std::sort(conns[am1[0]].begin(), conns[am1[0]].end());
        std::sort(am1.begin(), am1.end());
        auto lst = std::set_difference(lits.begin(), lits.end(), am1.begin(), am1.end(), lits.begin());
        if (lst < lits.end()) lits.resize(lst - lits.begin());
        for (auto &l : conns) {
            auto lst = std::set_difference(l.second.begin(), l.second.end(), am1.begin(), am1.end(), l.second.begin());
            if (lst < l.second.end()) l.second.resize(lst - l.second.begin());
        }
        if (am1.size() > 1) {
            Minisat::vec<Lit> cls;
            vec<int> ind;
            Int min_Cs = Int_MAX;
            for (Lit p : am1) {
                int l = std::lower_bound(&assump_ps[0], &assump_ps[0]+assump_ps.size(), p) - &assump_ps[0];
                if (l >= 0 && l < assump_ps.size() && assump_ps[l] == p) {
                    ind.push(l);
                    if (assump_Cs[l] < min_Cs) min_Cs = assump_Cs[l];
                }
            }
            for (unsigned i = 0; i < am1.size(); i++)
                if (assump_Cs[ind[i]] == min_Cs) cls.push(am1[i]), assump_Cs[ind[i]] = -assump_Cs[ind[i]];
                else {
                    Lit r = mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true);
                    sat_solver.addClause(am1[i], r);
                    cls.push(~r);
                    assump_Cs[ind[i]] -= min_Cs;
                }
            Lit r = mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true);
            sat_solver.setFrozen(var(r), true);
            cls.push(r); assump_ps.push(~r); assump_Cs.push(min_Cs);
            sat_solver.addClause(cls);
            am1_cnt++; am1_len_sum += am1.size();  LB_goalvalue += min_Cs;
        }
    }
    if (am1_cnt > 0 || confl.size() > 0) clear_assumptions(assump_ps, assump_Cs);
    if (opt_verbosity >= 2 && am1_cnt > 0) 
        reportf("Found %d AtMostOne cores of avg size: %.2f\n", am1_cnt, (double)am1_len_sum/am1_cnt);
}

