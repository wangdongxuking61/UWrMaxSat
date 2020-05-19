#ifndef SatSolver_h
#define SatSolver_h

#include "minisat/mtl/Vec.h"
#include "minisat/simp/SimpSolver.h"

#if defined(GLUCOSE3) || defined(GLUCOSE4)
namespace Minisat = Glucose;
#endif
#ifdef GLUCOSE4
#define rnd_decisions stats[14]
#define max_literals  stats[21]
#define tot_literals  stats[22]
#endif

#ifdef MAPLE
#define uncheckedEnqueue(p) uncheckedEnqueue(p,decisionLevel())
#endif

using Minisat::Var;
using Minisat::Lit;
using Minisat::SimpSolver;
using Minisat::lbool;
using Minisat::mkLit;
using Minisat::lit_Undef;
#ifdef MINISAT
using Minisat::l_Undef;
using Minisat::l_True;
using Minisat::l_False;
using Minisat::var_Undef;
#define VAR_UPOL l_Undef
#define LBOOL    lbool
#else
#define VAR_UPOL true
#define LBOOL
#endif

#ifdef BIG_WEIGHTS
using weight_t = Int; 
#define WEIGHT_MAX Int_MAX
#else
using weight_t = int64_t;
#define WEIGHT_MAX std::numeric_limits<weight_t>::max()
#endif

class ExtSimpSolver: public SimpSolver {
public:
    void printVarsCls(bool encoding = true, const vec<Pair<weight_t, Minisat::vec<Lit>* > > *soft_cls = NULL, int soft_cls_sz = 0);
    bool prop_check   (const Minisat::vec<Lit>& assumps, Minisat::vec<Lit>& prop, int psaving = 0); // compute a list of propagated literals given a set of assumptions
};

#endif
