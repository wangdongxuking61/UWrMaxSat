#include "SatSolver.h"

static Var mapVar(Var x, Minisat::vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void ExtSimpSolver::printVarsCls(bool encoding, const vec<Pair<weight_t, Minisat::vec<Lit>* > > *soft_cls, int soft_cnt)
{
    Minisat::vec<Var> map; Var max=0;
    int cnt;

    if (!ok) max=1, cnt=2;
    else {
        cnt = assumptions.size();
        for (int i = 0; i < clauses.size(); i++)
          if (!satisfied(ca[clauses[i]])) {
	      cnt++;
              Minisat::Clause& c = ca[clauses[i]];
	      for (int j = 0; j < c.size(); j++)
	          if (value(c[j]) != l_False)
	              mapVar(var(c[j]), map, max);
        }
        if (soft_cls != NULL)
            for (int i = 0; i < soft_cls->size(); i++) {
                Minisat::vec<Lit>& c = *(*soft_cls)[i].snd;
                for (int j = 0; j < c.size(); j++)
	            if (value(c[j]) != l_False)
	                mapVar(var(c[j]), map, max);
            }

    }
    printf("c ============================[ %s Statistics ]============================\n", 
            encoding ? "Encoding" : " Problem");
    printf("c |  Number of variables:  %12d                                         |\n", max);
    if (soft_cnt == 0)
        printf("c |  Number of clauses:    %12d                                         |\n", cnt);
    else
        printf("c |  Number of clauses:    %12d (incl. %12d soft in queue)      |\n", cnt + soft_cnt, soft_cnt);
    printf("c ===============================================================================\n");
}

//=================================================================================================
// Propagate and check:
bool ExtSimpSolver::prop_check(const Minisat::vec<Lit>& assumps, Minisat::vec<Lit>& prop, int psaving)
{
    using Minisat::CRef; using Minisat::CRef_Undef;
    prop.clear();

    if (!ok)
        return false;

    bool    st = true;
#ifdef MAPLE
    int trailRec = trailRecord;
    trailRecord = trail.size();
#else    
    int  level = decisionLevel();
#endif
    CRef confl = CRef_Undef;

    // dealing with phase saving
    int psaving_copy = phase_saving;
    phase_saving = psaving;

    // propagate each assumption at a new decision level
    for (int i = 0; st && confl == CRef_Undef && i < assumps.size(); ++i) {
        Lit p = assumps[i];

        if (value(p) == l_False)
            st = false;
        else if (value(p) != l_True) {
#ifdef MAPLE
            Solver::simpleUncheckEnqueue(p);
            confl = Solver::simplePropagate();
#else
            Solver::newDecisionLevel ();
            Solver::uncheckedEnqueue(p);
            confl = Solver::propagate();
#endif
        }
    }

    // copying the result
#ifdef MAPLE
    if (trail.size() > trailRec) {
        for (int c = trailRec; c < trail.size(); c++)
#else
    if (decisionLevel() > level) {
        for (int c = trail_lim[level]; c < trail.size(); ++c)
#endif            
            prop.push(trail[c]);

        // if there is a conflict, pushing
        // the conflicting literal as well
        if (confl != CRef_Undef)
            prop.push(ca[confl][0]);

        // backtracking
#ifdef MAPLE
        cancelUntilTrailRecord();
        trailRecord = trailRec;
#else
        Solver::cancelUntil(level);
#endif
    }

    // restoring phase saving
    phase_saving = psaving_copy;

    return st && confl == CRef_Undef;
}
