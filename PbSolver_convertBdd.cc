/**************************************************************************[PbSolver_convertBdd.cc]
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

#include "PbSolver.h"
#include "FEnv.h"
#include "Debug.h"


//=================================================================================================

#define lit2fml(p) id(var(var(p)),sign(p))

static
Pair<Pair<Interval<Int>,Interval<Int> >, Formula> 
buildBDD_i(const vec<Lit>& ps, const vec<Int>& Cs, Int lo, Int hi, int size, Int sum, Int material_left,
	   vec<std::map<Pair< Interval<Int> , Interval<Int> >, Formula> > &memo, int max_cost)
{
    Int lower_limit = (lo == Int_MIN) ? Int_MIN : lo - sum;
    Int upper_limit = Int_MAX;
    // lo - sum <= (Cs[0]*ps[0] + ... + Cs[size-1]*ps[size-1]) <= hi - sum

    if (FEnv::topSize() > max_cost)
      return Pair_new(Pair_new(Interval_new(lower_limit,lower_limit),
                               Interval_new(upper_limit,upper_limit) ),
                      _undef_);     // (mycket elegant!)

    if ((lower_limit <= 0 && upper_limit >= material_left) || lower_limit > material_left || upper_limit < 0) {
      Interval<Int> lower_interval;
      Interval<Int> upper_interval;
      Formula fm;  Int zero = 0;  Int minus_one = -1; 

      if (lower_limit <= 0)
        lower_interval = Interval_new(Int_MIN,zero);
      else
        lower_interval = Interval_new(material_left + 1, Int_MAX); 

      if (upper_limit >= 0)
        upper_interval = Interval_new(material_left, Int_MAX);
      else
        upper_interval = Interval_new(Int_MIN, minus_one);

      if (lower_limit <= 0 && upper_limit >= material_left)
        fm = _1_ ;
      else 
        fm = _0_ ;
      return Pair_new( Pair_new(lower_interval,upper_interval), fm);
    }

    Pair<Pair<Interval<Int>,Interval<Int> >, Formula> result;
    Pair<Interval<Int>,Interval<Int> > intervals
      = Pair_new(Interval_new(lower_limit,lower_limit),
     Interval_new(upper_limit,upper_limit));

    Formula fm;
    auto search = memo[size].find(intervals);
    
    if (search == memo[size].end()) {
      assert(size > 0);
      size--;
      material_left -= Cs[size];

      Pair< Pair< Interval<Int>, Interval<Int> >, Formula> 
      tt = buildBDD_i(ps, Cs, lo, hi, size, sum + Cs[size], material_left, memo, max_cost);
      if (tt.snd == _undef_) // return _undef_;
        return tt;

      Pair< Pair< Interval<Int>, Interval<Int> >, Formula> 
      ff = buildBDD_i(ps, Cs, lo, hi, size, sum, material_left, memo, max_cost);
      if (ff.snd == _undef_) //return _undef_;
        return ff;

      Int tt_lo_beta = tt.fst.fst.fst, tt_lo_gamma = tt.fst.fst.snd;
      Int ff_lo_beta = ff.fst.fst.fst, ff_lo_gamma = ff.fst.fst.snd;
      Int tt_hi_beta = tt.fst.snd.fst, tt_hi_gamma = tt.fst.snd.snd;
      Int ff_hi_beta = ff.fst.snd.fst, ff_hi_gamma = ff.fst.snd.snd;

      intervals = Pair_new(Interval_new(max(tt_lo_beta.add(Cs[size]),ff_lo_beta), min(tt_lo_gamma.add(Cs[size]),ff_lo_gamma)),
        Interval_new(max(tt_hi_beta.add(Cs[size]),ff_hi_beta), min(tt_hi_gamma.add(Cs[size]),ff_hi_gamma)));

      if(tt.snd != ff.snd) {
        //if(!opt_convert_bdd_monotonic)
        //  fm = ITE(lit2fml(ps[size]), tt.snd, ff.snd);
        /*else*/if(intervals.snd.snd == Int_MAX)
          fm = ITEn(lit2fml(ps[size]), tt.snd, ff.snd);
        else if(intervals.fst.fst == Int_MIN)
          fm = ITEp(lit2fml(ps[size]), tt.snd, ff.snd);
        else          // only negative side NOW ##
          fm = ITE(lit2fml(ps[size]), tt.snd, ff.snd);
      } else fm = tt.snd;

      memo[size+1][intervals] = fm;
      result = Pair_new(intervals, fm);
    } else {
      result = Pair_new(search->first, search->second);
    }

    return result;
}

// New school: Use the new 'ITE' construction of the formula environment 'FEnv'.
//
Formula convertToBdd_one(vec<Lit>& ls, vec<Int>& Cs, Int lo, Int hi, int max_cost)
{
  Int sum = 0;
  Formula ret;

  for (int j = 0; j < ls.size(); j++) sum += Cs[j];

  FEnv::push();

  vec<std::map<Pair< Interval<Int> , Interval<Int> >,  Formula> > memo(Cs.size()+1);
  ret = buildBDD_i(ls, Cs, lo, hi, Cs.size(), 0, sum, memo, max_cost).snd;

  if (ret == _undef_)
    FEnv::pop();
  else {
    if (opt_verbosity >= 1)
      /**/ reportf("BDD-cost:%5d\n", FEnv::topSize());
    FEnv::keep();
  }

  return ret;
}

Formula convertToBdd(const Linear& c, int max_cost)
{
  vec<Lit> ls;
  vec<Int> Cs;
  Int csum = 0;
  Formula ret;

  for (int j = 0; j < c.size; j++)
    ls.push(c[j]), Cs.push(c(j)), csum += c(j);

    ret = convertToBdd_one(ls, Cs, c.lo, Int_MAX, max_cost);    
    if(ret == _undef_ ) return ret;

    if(c.hi != Int_MAX) {
      ls.clear(); Cs.clear();
      for(int i=0; i<c.size; i++)
        ls.push(~c[i]), Cs.push(c(i));
      ret &= convertToBdd_one(ls, Cs, csum - c.hi, Int_MAX, max_cost);
    }

  return ret == _undef_ || c.lit == lit_Undef ? ret : ~lit2fml(c.lit) | ret ;
}
