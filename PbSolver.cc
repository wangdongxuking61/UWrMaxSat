/*************************************************************************************[PbSolver.cc]
Copyright (c) 2005-2010, Niklas Een, Niklas Sorensson

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

extern int verbosity;


//=================================================================================================
// Interface required by parser:


int PbSolver::getVar(cchar* name)
{
    int ret;
    if (!name2index.peek(name, ret)){
        // Create new variable:
        Var x = index2name.size();
        index2name.push(xstrdup(name));
        n_occurs  .push(0);
        n_occurs  .push(0);
        //assigns   .push(toInt(l_Undef));
        sat_solver.newVar();        // (reserve one SAT variable for each PB variable)
        ret = name2index.set(index2name.last(), x);
    }
    return ret;
}


void PbSolver::allocConstrs(int n_vars, int n_constrs)
{
    declared_n_vars    = n_vars;
    declared_n_constrs = n_constrs;
}


void PbSolver::addGoal(const vec<Lit>& ps, const vec<Int>& Cs)
{
    /**/debug_names = &index2name;
    //**/reportf("MIN: "); dump(ps, Cs); reportf("\n");

    goal = new (xmalloc<char>(sizeof(Linear) + ps.size()*(sizeof(Lit) + sizeof(Int)))) Linear(ps, Cs, Int_MIN, Int_MAX, lit_Undef);
}

bool PbSolver::addConstr(const vec<Lit>& ps, const vec<Int>& Cs, Int rhs, int ineq, Lit lit) {
  vec<Lit>    norm_ps;
  vec<Int>    norm_Cs;
  Int         norm_rhs;
  Lit         norm_lit;

  #define Copy    do{ norm_ps.clear(); norm_Cs.clear(); for (int i = 0; i < ps.size(); i++) norm_ps.push(ps[i]), norm_Cs.push( Cs[i]); norm_rhs =  rhs;  norm_lit = lit; }while(0)
  #define CopyInv do{ norm_ps.clear(); norm_Cs.clear(); for (int i = 0; i < ps.size(); i++) norm_ps.push(ps[i]), norm_Cs.push(-Cs[i]); norm_rhs = -rhs;  norm_lit = lit; }while(0)

  // non-normalize ORIGINAL
  if (ineq == 0){

    Copy;
    if (normalizePb(norm_ps, norm_Cs, norm_rhs, norm_lit))
      storePb(norm_ps, norm_Cs, norm_rhs, Int_MAX, norm_lit);

    CopyInv;
    if (normalizePb(norm_ps, norm_Cs, norm_rhs, norm_lit))
      storePb(norm_ps, norm_Cs, norm_rhs, Int_MAX, norm_lit);
  }else{
    if (ineq > 0)
      Copy;
    else {
      CopyInv;
      ineq = -ineq;
    }
    if (ineq == 2)
      ++norm_rhs;

    if (normalizePb(norm_ps, norm_Cs, norm_rhs, norm_lit))
      storePb(norm_ps, norm_Cs, norm_rhs, Int_MAX, norm_lit);
  }
  return okay();
}

//=================================================================================================


static Int gcd(Int small, Int big) {
    return (small == 0) ? big: gcd(big % small, small); }

// Normalize a PB constraint to only positive constants. Depends on:
//
//   bool    ok            -- Will be set to FALSE if constraint is unsatisfiable.
//   lbool   value(Lit)    -- Returns the value of a literal (however, it is sound to always return 'l_Undef', but produces less efficient results)
//   bool    addUnit(Lit)  -- Enqueue unit fact for propagation (returns FALSE if conflict detected).
//
// The two vectors 'ps' and 'Cs' (which are modififed by this method) should be interpreted as:
//
//   'p[0]*C[0] + p[1]*C[1] + ... + p[N-1]*C[N-1] >= C[N]'
//
// The method returns TRUE if constraint was normalized, FALSE if the constraint was already
// satisfied or determined contradictory. The vectors 'ps' and 'Cs' should ONLY be used if
// TRUE is returned.
//

bool PbSolver::normalizePb(vec<Lit>& ps, vec<Int>& Cs, Int& C, Lit lit)
{
    assert(ps.size() == Cs.size());
    if (!okay()) return false;

    // Remove assigned literals and literals with zero coefficients:
    int new_sz = 0;
    for (int i = 0; i < ps.size(); i++){
        if (value(ps[i]) != l_Undef){
            if (value(ps[i]) == l_True)
                C -= Cs[i];
        }else if (Cs[i] != 0){
            ps[new_sz] = ps[i];
            Cs[new_sz] = Cs[i];
            new_sz++;
        }
    }
    ps.shrink(ps.size() - new_sz);
    Cs.shrink(Cs.size() - new_sz);

    // Group all x/~x pairs
    //
    Map<Var, Pair<Int,Int> >    var2consts(Pair_new(0,0));     // Variable -> negative/positive polarity constant
    for (int i = 0; i < ps.size(); i++){
        Var             x      = var(ps[i]);
        Pair<Int,Int>   consts = var2consts.at(x);
        if (sign(ps[i]))
            consts.fst += Cs[i];
        else
            consts.snd += Cs[i];
        var2consts.set(x, consts);
    }

    // Normalize constants to positive values only:
    //
    vec<Pair<Var, Pair<Int,Int> > > all;
    var2consts.pairs(all);
    vec<Pair<Int,Lit> > Csps(all.size());
    for (int i = 0; i < all.size(); i++){
        if (all[i].snd.fst < all[i].snd.snd){
            // Negative polarity will vanish
            C -= all[i].snd.fst;
            Csps[i] = Pair_new(all[i].snd.snd - all[i].snd.fst, mkLit(all[i].fst));
        }else{
            // Positive polarity will vanish
            C -= all[i].snd.snd;
            Csps[i] = Pair_new(all[i].snd.fst - all[i].snd.snd, ~mkLit(all[i].fst));
        }
    }

    // Sort literals on growing constant values:
    //
    sort(Csps);     // (use lexicographical order of 'Pair's here)
    Int     sum = 0;
    for (int i = 0; i < Csps.size(); i++){
        Cs[i] = Csps[i].fst, ps[i] = Csps[i].snd, sum += Cs[i];
        if (sum < 0) fprintf(stderr, "ERROR! Too large constants encountered in constraint.\n"), exit(1);
    }
    ps.shrink(ps.size() - Csps.size());
    Cs.shrink(Cs.size() - Csps.size());

    // Propagate already present consequences:
    //
    bool changed;
    do{
        changed = false;
        while (ps.size() > 0 && sum-Cs.last() < C){
            changed = true;
            if (lit != lit_Undef) {
              vec<Lit> ban;
              ban.push( ~lit );
              ban.push(ps.last());
              addClause(ban);
            } else if (!addUnit(ps.last())) {
              sat_solver.addEmptyClause();
              return false;
            }
            sum -= Cs.last();
            C   -= Cs.last();
            ps.pop(); Cs.pop();
        }

        // Trivially true or false?
        if (C <= 0)
          return false;
        if (sum < C) {
            if (lit != lit_Undef) 
                addUnit(~lit);
            else sat_solver.addEmptyClause();
            return false;
        }
        assert(sum - Cs[ps.size()-1] >= C);

        // GCD:
        assert(Cs.size() > 0);
        Int     div = Cs[0];
        for (int i = 1; i < Cs.size(); i++)
            div = gcd(div, Cs[i]);
        for (int i = 0; i < Cs.size(); i++)
            Cs[i] /= div;
        C = (C + div-1) / div;
        if (div != 1)
            changed = true;

        // Trim constants:
        for (int i = 0; i < Cs.size(); i++)
            if (Cs[i] > C)
                changed = true,
                Cs[i] = C;
    }while (changed);

    return true;
}

void PbSolver::storePb(const vec<Lit>& ps, const vec<Int>& Cs, Int lo, Int hi, Lit lit)
{
    assert(ps.size() == Cs.size());
    for (int i = 0; i < ps.size(); i++)
        if (toInt(ps[i]) < n_occurs.size()) n_occurs[toInt(ps[i])]++;

    if (lit!=lit_Undef && n_occurs.size() > toInt(lit))
        n_occurs[toInt(lit)]++;

    constrs.push(new (mem.alloc(sizeof(Linear) + ps.size()*(sizeof(Lit) + sizeof(Int)))) Linear(ps, Cs, lo, hi, lit));
}

//=================================================================================================


// Returns TRUE if the constraint should be deleted. May set the 'ok' flag to false
bool PbSolver::propagate(Linear& c)
{
    //**/reportf("BEFORE propagate()\n");
    //**/dump(c, sat_solver.assigns_ref()); reportf("\n");

    // Remove assigned literals:
    Int     sum = 0, true_sum = 0;
    int     j = 0;
    for (int i = 0; i < c.size; i++){
        assert(c(i) > 0);
        if (value(c[i]) == l_Undef){
            sum += c(i);
            c(j) = c(i);
            c[j] = c[i];
            j++;
        }else if (value(c[i]) == l_True)
            true_sum += c(i);
    }
    c.size = j;
    if (c.lo != Int_MIN) c.lo -= true_sum;
    if (c.hi != Int_MAX) c.hi -= true_sum;

    // Propagate:
    while (c.size > 0){
        if (c(c.size-1) > c.hi){
            addUnit(~c[c.size-1]);
            sum -= c(c.size-1);
            c.size--;
        }else if (sum - c(c.size-1) < c.lo){
            addUnit(c[c.size-1]);
            sum -= c(c.size-1);
            if (c.lo != Int_MIN) c.lo -= c(c.size-1);
            if (c.hi != Int_MAX) c.hi -= c(c.size-1);
            c.size--;
        }else
            break;
    }

    if (c.lo <= 0)  c.lo = Int_MIN;
    if (c.hi > sum) c.hi = Int_MAX;

    //**/reportf("AFTER propagate()\n");
    //**/dump(c, sat_solver.assigns_ref()); reportf("\n\n");
    if (c.size == 0){
        if (c.lo > 0 || c.hi < 0)
            sat_solver.addEmptyClause();
        return true;
    }else
        return c.lo == Int_MIN && c.hi == Int_MAX;
}


void PbSolver::propagate()
{
    if (nVars() == 0) return;
    if (occur.size() == 0) setupOccurs();

    if (opt_verbosity >= 2) reportf("  -- Unit propagations: ", constrs.size());
    bool found = false;

    while (propQ_head < trail.size()){
        //**/reportf("propagate("); dump(trail[propQ_head]); reportf(")\n");
        Var     x = var(trail[propQ_head++]);
        for (int pol = 0; pol < 2; pol++){
            vec<int>&   cs = occur[toInt(mkLit(x,pol))];
            for (int i = 0; i < cs.size(); i++){
                if (constrs[cs[i]] == NULL) continue;
                int trail_sz = trail.size();
                if (propagate(*constrs[cs[i]]))
                    constrs[cs[i]] = NULL;
                if (opt_verbosity >= 2 && trail.size() > trail_sz) found = true, reportf("p");
                if (!okay()) return;
            }
        }
    }

    if (opt_verbosity >= 2) {
        if (!found) reportf("(none)\n");
        else        reportf("\n");
    }

    occur.clear(true);
}


void PbSolver::setupOccurs()
{
    // Allocate vectors of right capacities:
    occur.growTo(nVars()*2);
    assert(nVars() == pb_n_vars);
    for (int i = 0; i < nVars()*2; i++){
        vec<int> tmp(xmalloc<int>(n_occurs[i]), n_occurs[i]); tmp.clear();
        tmp.moveTo(occur[i]); }

    // Fill vectors:
    for (int i = 0; i < constrs.size(); i++){
        if (constrs[i] == NULL) continue;
        for (int j = 0; j < constrs[i]->size; j++)
            assert(occur[toInt((*constrs[i])[j])].size() < n_occurs[toInt((*constrs[i])[j])]),
            occur[toInt((*constrs[i])[j])].push(i);
    }
}


// Left-hand side equal
static bool lhsEq(const Linear& c, const Linear& d) {
    if (c.size == d.size){
        for (int i = 0; i < c.size; i++) if (c[i] != d[i] || c(i) != d(i)) return false;
        return true;
    }else return false; }
// Left-hand side equal complementary (all literals negated)
static bool lhsEqc(const Linear& c, const Linear& d) {
    if (c.size == d.size){
        for (int i = 0; i < c.size; i++) if (c[i] != ~d[i] || c(i) != d(i)) return false;
        return true;
    }else return false; }


void PbSolver::findIntervals()
{
    if (opt_verbosity >= 2)
        reportf("  -- Detecting intervals from adjacent constraints: ");

    bool found = false;
    int i = 0;
    Linear* prev;
    for (; i < constrs.size() && constrs[i] == NULL; i++);
    if (i < constrs.size()){
        prev = constrs[i++];
        for (; i < constrs.size(); i++){
            if (constrs[i] == NULL) continue;
            Linear& c = *prev;
            Linear& d = *constrs[i];

            if (lhsEq(c, d)){
                if (d.lo < c.lo) d.lo = c.lo;
                if (d.hi > c.hi) d.hi = c.hi;
                constrs[i-1] = NULL;
                if (opt_verbosity >= 2) reportf("=");
                found = true;
            }
            if (lhsEqc(c, d)){
                Int sum = 0;
                for (int j = 0; j < c.size; j++)
                    sum += c(j);
                Int lo = (c.hi == Int_MAX) ? Int_MIN : sum - c.hi;
                Int hi = (c.lo == Int_MIN) ? Int_MAX : sum - c.lo;
                if (d.lo < lo) d.lo = lo;
                if (d.hi > hi) d.hi = hi;
                constrs[i-1] = NULL;
                if (opt_verbosity >= 2) reportf("#");
                found = true;
            }

            prev = &d;
        }
    }
    if (opt_verbosity >= 2) {
        if (!found) reportf("(none)\n");
        else        reportf("\n");
    }
}


bool PbSolver::rewriteAlmostClauses()
{
    vec<Lit>    ps;
    vec<Int>    Cs;
    bool        found = false;
    int         n_splits = 0;
    char        buf[20];

    if (opt_verbosity >= 2)
        reportf("  -- Clauses(.)/Splits(s): ");
    for (int i = 0; i < constrs.size(); i++){
        if (constrs[i] == NULL) continue;
        Linear& c   = *constrs[i];
        assert(c.lo != Int_MIN || c.hi != Int_MAX);

        if (c.hi != Int_MAX) continue;

        int n = c.size;
        for (; n > 0 && c(n-1) == c.lo; n--);

        if (n <= 1){
            // Pure clause:
            if (opt_verbosity >= 2) reportf(".");
            found = true;
            ps.clear();
            for (int j = n; j < c.size; j++)
                ps.push(c[j]);
            addClause(ps);

            constrs[i] = NULL;      // Remove this clause

        }else if (c.size-n >= 3){
            // Split clause part:
            if (opt_verbosity >= 2) reportf("s");
            found = true;
            sprintf(buf, "@split%d", n_splits);
            n_splits++;
            Var x = getVar(buf); assert(x == sat_solver.nVars()-1);
            ps.clear();
            ps.push(mkLit(x));
            for (int j = n; j < c.size; j++)
                ps.push(c[j]);
            addClause(ps);
            if (!okay()){
                reportf("\n");
                return false; }

            ps.clear();
            Cs.clear();
            ps.push(~mkLit(x));
            Cs.push(c.lo);
            for (int j = 0; j < n; j++)
                ps.push(c[j]),
                Cs.push(c(j));
            if (!addConstr(ps, Cs, c.lo, 1, lit_Undef)){
                reportf("\n");
                return false; }

            constrs[i] = NULL;      // Remove this clause
        }
    }

    if (opt_verbosity >= 2) {
        if (!found) reportf("(none)\n");
        else        reportf("\n");
    }
    return true;
}


//=================================================================================================
// Main solver/optimizer:
static PbSolver *pb_solver;
static
void SIGINT_interrupt(int /*signum*/) { pb_solver->sat_solver.interrupt(); pb_solver->asynch_interrupt=true; }

static
Int evalGoal(Linear& goal, Minisat::vec<lbool>& model)
{
    Int sum = 0;
    for (int i = 0; i < goal.size; i++){
        assert(model[var(goal[i])] != l_Undef);
        if (( sign(goal[i]) && model[var(goal[i])] == l_False)
        ||  (!sign(goal[i]) && model[var(goal[i])] == l_True )
        )
            sum += goal(i);
    }
    return sum;
}

void PbSolver::solve(solve_Command cmd)
{
    if (!okay()) {
        if (opt_verbosity >= 1) sat_solver.printVarsCls();
        return;
    }

    // Convert constraints:
    pb_n_vars = nVars();
    pb_n_constrs = constrs.size();
    if (opt_verbosity >= 1)
        reportf("Converting %d PB-constraints to clauses...\n", constrs.size());
    propagate();
    if (!convertPbs(true)){
        if (opt_verbosity >= 1) sat_solver.printVarsCls();
        assert(!okay()); return; 
    }

    // Freeze goal function variables (for SatELite):
    if (goal != NULL){
        for (int i = 0; i < goal->size; i++)
            sat_solver.setFrozen(var((*goal)[i]), true);
    }

    // Solver (optimize):
    //sat_solver.setVerbosity(opt_verbosity);
    sat_solver.verbosity = opt_verbosity;
    Int goal_gcd;
    if (goal != NULL) {
        goal_gcd = (*goal)(0);
        for (int i = 1; i < goal->size; ++i) goal_gcd = gcd(goal_gcd, (*goal)(i));
        if (goal_gcd < 0) goal_gcd = -goal_gcd;
    }

    vec<Lit> goal_ps; if (goal != NULL){ for (int i = 0; i < goal->size; i++) goal_ps.push((*goal)[i]); }
    vec<Int> goal_Cs; if (goal != NULL){ for (int i = 0; i < goal->size; i++) goal_Cs.push((*goal)(i)/goal_gcd); }
    assert(best_goalvalue == Int_MAX);

    if (opt_polarity_sug != 0){
        for (int i = 0; i < goal_Cs.size(); i++){
            bool dir = goal_Cs[i]*opt_polarity_sug > 0 ? !sign(goal_ps[i]) : sign(goal_ps[i]);
            sat_solver.setPolarity(var(goal_ps[i]), /*lbool*/(dir));
        }
    }

    if (opt_convert_goal != ct_Undef)
        opt_convert = opt_convert_goal;
    opt_sort_thres *= opt_goal_bias;
    opt_shared_fmls = true;

    if (opt_goal != Int_MAX)
        addConstr(goal_ps, goal_Cs, opt_goal, -1, lit_Undef),
        convertPbs(false);

    if (opt_cnf != NULL)
        reportf("Exporting CNF to: \b%s\b\n", opt_cnf),
        sat_solver.toDimacs(opt_cnf),
        exit(0);

    pb_solver = this;
    signal(SIGINT, SIGINT_interrupt);
    signal(SIGXCPU,SIGINT_interrupt);

    bool    sat = false;
    Minisat::vec<Lit> assump_ps;
    Int     try_lessthan = opt_goal;
    int     n_solutions = 0;    // (only for AllSolutions mode)

    LB_goalvalue = 0, UB_goalvalue = 0; 
    if (goal != NULL)
        for (int i = 0; i < goal_Cs.size(); ++i)
            if (value(goal_ps[i]) != l_Undef) {
                if (value(goal_ps[i]) == l_True)
                    LB_goalvalue += goal_Cs[i], UB_goalvalue += goal_Cs[i];
	    } else if (goal_Cs[i] < 0) LB_goalvalue += goal_Cs[i];
            else UB_goalvalue += goal_Cs[i];
    if (opt_minimization != 0 && goal != NULL && opt_goal == Int_MAX) {
        Lit assump_lit = mkLit(sat_solver.newVar(true, !opt_branch_pbvars));
        try_lessthan = (UB_goalvalue + LB_goalvalue)/2;
        if (addConstr(goal_ps, goal_Cs, try_lessthan, -2, assump_lit))  assump_ps.push(assump_lit), convertPbs(false);
    }
    if (opt_verbosity >= 1)
        sat_solver.printVarsCls();

    while (1) {
      if (asynch_interrupt) { reportf("Interrupted ***\n"); break; }
      if (sat_solver.solve(assump_ps)) { // SAT returned
        if(assump_ps.size() > 0) {
          assert(assump_ps.size() == 1);
          addUnit(assump_ps[0]);
        }
        assump_ps.clear();
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
            best_model.clear();
            for (Var x = 0; x < pb_n_vars; x++)
                assert(sat_solver.model[x] != l_Undef),
                best_model.push(sat_solver.model[x] == l_True);
            if (goal == NULL)   // ((fix: moved here Oct 4, 2005))
                break;

            best_goalvalue = evalGoal(*goal, sat_solver.model) / goal_gcd;
            if (opt_satlive || opt_verbosity == 0) { 
                printf("o %s\n", toString(best_goalvalue * goal_gcd)); fflush(stdout); }
            if (cmd == sc_FirstSolution) break;

            if (opt_verbosity >= 1 && !opt_satlive){
                char* tmp = toString(best_goalvalue * goal_gcd);
                reportf("\bFound solution: %s\b\n", tmp);
                xfree(tmp); }
            if(opt_minimization == 0 || best_goalvalue - LB_goalvalue < opt_seq_thres) {
                try_lessthan = best_goalvalue;
                if (!addConstr(goal_ps, goal_Cs, best_goalvalue, -2, lit_Undef))
                    break;
            } else {
                Lit assump_lit = mkLit(sat_solver.newVar(true, !opt_branch_pbvars));

                try_lessthan = (LB_goalvalue*(100-opt_bin_percent) + best_goalvalue*(opt_bin_percent))/100;

                if (!addConstr(goal_ps, goal_Cs, try_lessthan, -2, assump_lit))
                    break; // unsat

                assump_ps.push(assump_lit);
            }
            convertPbs(false);
        }
      } else { // UNSAT returned

        if (assump_ps.size() == 0) break;

        assert(assump_ps.size() == 1);
        addUnit(~(assump_ps[0]));
        assump_ps.clear();
        LB_goalvalue = try_lessthan;

	if(opt_minimization != 2 || best_goalvalue == Int_MAX || best_goalvalue - LB_goalvalue < opt_seq_thres) {
	  try_lessthan = (best_goalvalue != Int_MAX ? best_goalvalue : UB_goalvalue+1);
	  if (!addConstr(goal_ps, goal_Cs, try_lessthan, -2, lit_Undef))
	    break;
	} else {
	  Lit assump_lit = mkLit(sat_solver.newVar(true, !opt_branch_pbvars));

	  try_lessthan = (LB_goalvalue*(100-opt_bin_percent) + best_goalvalue*(opt_bin_percent))/100;

	  if (!addConstr(goal_ps, goal_Cs, try_lessthan, -2, assump_lit))
	    break; // unsat

	  assump_ps.push(assump_lit);
	}
        if (opt_minimization >= 1 && opt_verbosity >= 2)
            reportf("Lower bound  = %s\n", toString(LB_goalvalue));
        convertPbs(false);
      }         
    } // END OF LOOP

    if (goal == NULL && sat)
        best_goalvalue = Int_MIN;       // (found model, but don't care about it)
    if (opt_verbosity >= 1){
        if      (!sat)
            reportf(asynch_interrupt ? "\bUNKNOWN\b\n" : "\bUNSATISFIABLE\b\n");
        else if (goal == NULL)
            reportf("\bSATISFIABLE: No goal function specified.\b\n");
        else if (cmd == sc_FirstSolution){
            char* tmp = toString(best_goalvalue * goal_gcd);
            reportf("\bFirst solution found: %s\b\n", tmp);
            xfree(tmp);
        }else if (asynch_interrupt){
            char* tmp = toString(best_goalvalue * goal_gcd);
            reportf("\bSATISFIABLE: Best solution found: %s\b\n", tmp);
            xfree(tmp);
       }else{
            char* tmp = toString(best_goalvalue * goal_gcd);
            reportf("\bOptimal solution: %s\b\n", tmp);
            xfree(tmp);
        }
    }
}

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
}

template <class T> struct LT {bool operator()(T x, T y) { return x.snd->last() < y.snd->last(); }};

void PbSolver::maxsat_solve(solve_Command cmd)
{
    if (!okay()) {
        if (opt_verbosity >= 1) sat_solver.printVarsCls();
        return;
    }

    // Convert constraints:
    pb_n_vars = nVars();
    pb_n_constrs = nClauses();

    // Freeze goal function variables (for SatELite):
    if (goal != NULL){
        for (int i = 0; i < goal->size; i++)
            sat_solver.setFrozen(var((*goal)[i]), true);
    }

    // Solver (optimize):
    //sat_solver.setVerbosity(opt_verbosity);
    sat_solver.verbosity = opt_verbosity;
    Int goal_gcd = 1;
    if (goal != NULL) {
        goal_gcd = (*goal)(0);
        for (int i = 1; i < goal->size; ++i) goal_gcd = gcd(goal_gcd, (*goal)(i));
        if (goal_gcd < 0) goal_gcd = -goal_gcd;
        if (goal_gcd != 1) {
            if (LB_goalvalue != Int_MIN) LB_goalvalue /= goal_gcd;
            if (UB_goalvalue != Int_MAX) UB_goalvalue /= goal_gcd;
        }
    }

    assert(best_goalvalue == Int_MAX);

    if (goal != NULL && opt_polarity_sug != 0){
        for (int i = 0; i < goal->size; i++){
            bool dir = (*goal)(i)*opt_polarity_sug > 0 ? !sign((*goal)[i]) : sign((*goal)[i]);
            sat_solver.setPolarity(var((*goal)[i]), /*lbool*/(dir));
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
    vec<Linear*> saved_constrs;
    vec<Lit> goal_ps;
    Minisat::vec<Lit> assump_ps;
    vec<Int> goal_Cs, assump_Cs, sorted_assump_Cs, saved_constrs_Cs;
    bool    sat = false;
    Minisat::Lit inequality = lit_Undef, max_assump = lit_Undef;
    Int     try_lessthan = opt_goal, max_assump_Cs = Int_MIN;
    int     n_solutions = 0;    // (only for AllSolutions mode)

    Int LB_goalval = 0, UB_goalval = 0, fixed_goalval = 0;    
    if (goal != NULL) {
        vec<Pair<Lit,Int> > psCs;
        for (int i = 0; i < goal->size; ++i)
            if (value((*goal)[i]) != l_Undef) {
                if (value((*goal)[i]) == l_True) {
                    fixed_goalval += (*goal)(i);
                    addUnit((*goal)[i]);
                } else addUnit(~(*goal)[i]);
	    } else { 
                if ((*goal)(i) < 0) LB_goalval += (*goal)(i);
                else                UB_goalval += (*goal)(i);
                psCs.push(Pair_new(~(*goal)[i], (*goal)(i)/goal_gcd));
            }
        LB_goalval += fixed_goalval, UB_goalval += fixed_goalval;
        if (goal_gcd != 1) LB_goalval /= goal_gcd, UB_goalval /= goal_gcd, fixed_goalval /= goal_gcd;
        sort(psCs);
        if (UB_goalvalue == Int_MAX) {
            for (int i = 0; i < psCs.size(); i++) sorted_assump_Cs.push(psCs[i].snd);
            sortUnique(sorted_assump_Cs);
            if (sorted_assump_Cs.size()  == 1) sorted_assump_Cs.clear();
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
                delete soft_cls[i].snd;
            }
            soft_cls.clear();
        } else {
            for (int i = soft_cls.size() - 1; i >= 0; i--) 
                for (int j = soft_cls[i].snd->size() - 1; j >= 0; j--) sat_solver.setFrozen(var((*soft_cls[i].snd)[j]), true);
            max_assump_Cs = sorted_assump_Cs.last();
            sorted_assump_Cs.pop();
            sort(soft_cls);
            int start = soft_cls.size() - 1;
            while (start >= 0 && soft_cls[start].fst >= max_assump_Cs) start--;
            start++;
            if (start < soft_cls.size()) {
                int sz = soft_cls.size() - start;
                sort(&soft_cls[start], sz, LT<Pair<Int, Minisat::vec<Lit>*> >());
                for (int i = start; i < soft_cls.size(); i++) {
                    Lit p = ~soft_cls[i].snd->last();
                    if (soft_cls[i].snd->size() > 1) sat_solver.addClause(*soft_cls[i].snd); else p = ~p;
                    assump_ps.push(p); assump_Cs.push(soft_cls[i].fst/goal_gcd);
                }
                soft_cls.shrink(sz);
            }
        }
        if (psCs.size() > 0) max_assump = psCs.last().fst;
        psCs.clear();
    }
    if (opt_verbosity >= 1)
        sat_solver.printVarsCls();
    while (1) {
      if (asynch_interrupt) { reportf("Interrupted ***\n"); break; }
      if (sat_solver.solve(assump_ps)) { // SAT returned
        Int lastCs = 1;
        if(opt_minimization != 1 && assump_ps.size() > 0 && assump_ps.last() == inequality) {
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
            best_model.clear();
            for (Var x = 0; x < pb_n_vars; x++)
                assert(sat_solver.model[x] != l_Undef),
                best_model.push(sat_solver.model[x] == l_True);
            if (goal == NULL)   // ((fix: moved here Oct 4, 2005))
                break;

            best_goalvalue = evalGoal(*goal, sat_solver.model) / goal_gcd;
            Int goal_diff = best_goalvalue - evalPsCs(goal_ps, goal_Cs, sat_solver.model);
            if (best_goalvalue < UB_goalvalue && (opt_minimization != 1 || sorted_assump_Cs.size() == 0)) {
                UB_goalvalue = best_goalvalue;
                char* tmp = toString(best_goalvalue * goal_gcd);
                if (opt_satlive || opt_verbosity == 0)
                    printf("o %s\n", tmp), fflush(stdout);
                else reportf("\bFound solution: %s\b\n", tmp);
                xfree(tmp); }

            if (cmd == sc_FirstSolution || (opt_minimization == 1 || UB_goalvalue == LB_goalvalue) && sorted_assump_Cs.size() == 0) break;

            if (opt_minimization == 1) {
                max_assump_Cs = sorted_assump_Cs.last();
                sorted_assump_Cs.pop();
                int start = soft_cls.size() - 1;
                while (start >= 0 && soft_cls[start].fst >= max_assump_Cs) start--;
                start++;
                if (start < soft_cls.size()) {
                    int sz = soft_cls.size() - start, to = 0, fr = sz;
                    sort(&soft_cls[start], sz, LT<Pair<Int, Minisat::vec<Lit>*> >());
                    assump_ps.growTo(assump_ps.size() + sz); assump_Cs.growTo(assump_Cs.size() + sz);
                    for (int i = assump_ps.size() - 1; i >= sz; i--) assump_ps[i] = assump_ps[i-sz], assump_Cs[i] = assump_Cs[i-sz];
                    for (int i = start; i < soft_cls.size(); i++) {
                        Lit p = ~soft_cls[i].snd->last();
                        if (soft_cls[i].snd->size() > 1) sat_solver.addClause(*soft_cls[i].snd); else p = ~p;
                        while (fr < assump_ps.size() && assump_ps[fr] <= p) assump_ps[to] = assump_ps[fr], assump_Cs[to++] = assump_Cs[fr++];
                        assump_ps[to] = p; assump_Cs[to++] = soft_cls[i].fst/goal_gcd;
                    }
                    soft_cls.shrink(sz);
                }
                continue;
            }
            if (opt_minimization == 0 || best_goalvalue - LB_goalvalue < opt_seq_thres) {
                //if (assump_ps.size() > 0) inequality = mkLit(sat_solver.newVar(true, !opt_branch_pbvars));
                inequality = lit_Undef;
                try_lessthan = best_goalvalue;
            } else {
                inequality = mkLit(sat_solver.newVar(true, !opt_branch_pbvars), true);
                try_lessthan = (LB_goalvalue*(100-opt_bin_percent) + best_goalvalue*(opt_bin_percent))/100;
            }
            if (!addConstr(goal_ps, goal_Cs, try_lessthan - goal_diff, -2, inequality))
                break; // unsat
            if (inequality != lit_Undef) assump_ps.push(inequality), assump_Cs.push(lastCs);
            convertPbs(false);
        }
      } else { // UNSAT returned
        if (assump_ps.size() == 0) break;
        if (sat_solver.conflict.size() > 0 && sat_solver.conflict.size() < 6) sat_solver.addClause(sat_solver.conflict);
        Int min_removed = Int_MAX;
        int removed = 0;
        bool other_conflict = false;

        if (opt_minimization == 1) { 
            goal_ps.clear(); goal_Cs.clear();
        }
        for (int i = 0; i < sat_solver.conflict.size(); i++) {
            Minisat::Lit p = ~sat_solver.conflict[i];
            int j = std::lower_bound(&assump_ps[0], &assump_ps[0] + assump_ps.size(), p) - &assump_ps[0];
            if (j >= 0 && j < assump_ps.size() && p == assump_ps[j]) { 
                if (opt_minimization == 1 || p <= max_assump) {
                    goal_ps.push(~p), goal_Cs.push(opt_minimization == 1 ? 1 : assump_Cs[j]);
                    if (assump_Cs[j] < min_removed) min_removed = assump_Cs[j];
                } else other_conflict = true; // if (min_removed != Int_MAX) min_removed = 0;
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
                                Lit newp = mkLit(sat_solver.newVar(true, !opt_branch_pbvars), true);
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
            LB_goalvalue = (min_removed == 0 ? next_sum(LB_goalvalue, goal_Cs) : 
                            min_removed == Int_MAX ? try_lessthan : LB_goalvalue + min_removed);
        } else if (opt_minimization == 1) LB_goalvalue = next_sum(LB_goalvalue, goal_Cs); 
        else LB_goalvalue = try_lessthan;

        if (LB_goalvalue == best_goalvalue && opt_minimization != 1) break;

        Int goal_diff = best_goalvalue == Int_MAX ? fixed_goalval : best_goalvalue - evalPsCs(goal_ps, goal_Cs, best_model);
        if (opt_minimization == 1) {
            inequality = mkLit(sat_solver.newVar(true, !opt_branch_pbvars), true);
            try_lessthan = goal_diff + 2; // LB_goalvalue+1;
            //if (LB_goalvalue > 100 || sat_solver.conflicts > 1000000) opt_minimization = 2;
	} else if (opt_minimization == 0 || best_goalvalue == Int_MAX || best_goalvalue - LB_goalvalue < opt_seq_thres) {
            inequality = lit_Undef;
	    try_lessthan = (best_goalvalue != Int_MAX ? best_goalvalue : UB_goalvalue+1);
	} else {
	    inequality = mkLit(sat_solver.newVar(true, !opt_branch_pbvars), true);
	    try_lessthan = (LB_goalvalue*(100-opt_bin_percent) + best_goalvalue*(opt_bin_percent))/100;
	}
 
        if (!addConstr(goal_ps, goal_Cs, try_lessthan - goal_diff, -2, inequality))
            break; // unsat
        if (inequality != lit_Undef) {
            assump_ps.push(inequality); assump_Cs.push(min_removed != Int_MAX && min_removed != 0 ? min_removed : 1);
        }
        if (constrs.size() > 0) convertPbs(false);
        if (opt_minimization == 1) {
            if (constrs.size() > 0 && constrs.last()->lit == inequality)
                saved_constrs.push(constrs.last()), assump_map.set(toInt(inequality),saved_constrs.size() - 1),
                saved_constrs_Cs.push(assump_Cs.last());
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
            if (j < saved_constrs.size()) saved_constrs.shrink(saved_constrs.size() - j), saved_constrs_Cs.shrink(saved_constrs_Cs.size() - j);
            constrs.clear();
        }
        if (opt_minimization >= 1 && opt_verbosity >= 2) 
            reportf("Lower bound  = %s\n", toString(LB_goalvalue));
      }         
    } // END OF LOOP

    if (goal_gcd != 1) {
        if (best_goalvalue != Int_MAX) best_goalvalue *= goal_gcd;
        if (LB_goalvalue   != Int_MIN) LB_goalvalue *= goal_gcd;
        if (UB_goalvalue   != Int_MAX) UB_goalvalue *= goal_gcd;
    }
    if (goal == NULL && sat)
        best_goalvalue = Int_MIN;       // (found model, but don't care about it)
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

void PbSolver::printStats()
{
    double cpu_time = Minisat::cpuTime();
    double mem_used = Minisat::memUsedPeak();
    printf("c restarts               : %" PRIu64"\n", sat_solver.starts);
    printf("c conflicts              : %-12" PRIu64"   (%.0f /sec)\n", sat_solver.conflicts   , sat_solver.conflicts   /cpu_time);
    printf("c decisions              : %-12" PRIu64"   (%4.2f %% random) (%.0f /sec)\n", sat_solver.decisions, (float)sat_solver.rnd_decisions*100 / (float)sat_solver.decisions, sat_solver.decisions   /cpu_time);
    printf("c propagations           : %-12" PRIu64"   (%.0f /sec)\n", sat_solver.propagations, sat_solver.propagations/cpu_time);
    printf("c conflict literals      : %-12" PRIu64"   (%4.2f %% deleted)\n", sat_solver.tot_literals, (sat_solver.max_literals - sat_solver.tot_literals)*100 / (double)sat_solver.max_literals);
    if (mem_used != 0) printf("c Memory used            : %.2f MB\n", mem_used);
    printf("c CPU time               : %g s\n", cpu_time);
    printf("c Constr Enc: Srt/BDD/Add: %llu %llu %llu\n", srtEncodings, bddEncodings, addEncodings);
    printf("c OptExp Enc: Srt/BDD/Add: %llu %llu %llu\n", srtOptEncodings, bddOptEncodings, addOptEncodings);
}
