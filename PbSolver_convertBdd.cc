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


static
//Formula buildBDD(const Linear& c, int size, int lower_limit, int upper_limit, int material_left, Map<Pair<int,Int>,Formula>& memo, int max_cost)
Formula buildBDD(const Linear& c, int size, Int sum, Int material_left, Map<Pair<int,Int>,Formula>& memo, int max_cost, bool rightmost) // optimizing rightmmost path - M. Piotrów 13.10.2017
{
    Int lower_limit = (c.lo == Int_MIN) ? Int_MIN : c.lo - sum;
    Int upper_limit = (c.hi == Int_MAX) ? Int_MAX : c.hi - sum;

    if (lower_limit <= 0 && upper_limit >= material_left)
        return _1_;
    else if (lower_limit > material_left || upper_limit < 0)
        return _0_;
    //else if (FEnv::topSize() > max_cost)
    //    return _undef_;     // (mycket elegant!)

    static int prime = 974213;                         // M. Piotrów 13.10.2017
    Pair<int,Int>   key = Pair_new(size*prime, lower_limit);
    Formula         ret;

    if (!memo.peek(key, ret)){
        assert(size != 0);
        size--;
        material_left -= c(size);
        Int hi_sum = sign(c[size]) ? sum : sum + c(size);
        Int lo_sum = sign(c[size]) ? sum + c(size) : sum;
        Formula hi = buildBDD(c, size, hi_sum, material_left, memo, max_cost, false);
        if (hi == _undef_) return _undef_;
        Formula lo = buildBDD(c, size, lo_sum, material_left, memo, max_cost, rightmost);
        if (lo == _undef_) return _undef_;
        ret = ITE(var(var(c[size])), hi, lo);
	if (FEnv::topSize() > max_cost) return _undef_; // M. Piotrów 13.10.2017
        if (!rightmost) memo.set(key, ret);             // M. Piotrów 13.10.2017
    }
    return ret;
}


// New school: Use the new 'ITE' construction of the formula environment 'FEnv'.
//
Formula convertToBdd(const Linear& c, int max_cost)
{
    Map<Pair<int,Int>, Formula> memo(_undef_,c.size);

    Int sum = 0;
    for (int j = 0; j < c.size; j++)
        sum += c(j);

    FEnv::push();
    Formula ret = buildBDD(c, c.size, 0, sum, memo, max_cost, true);
    if (ret == _undef_)
        FEnv::pop();
    else{
        if (opt_verbosity >= 1)
            // reportf("BDD-cost:%5d\n", FEnv::topSize());
        FEnv::keep();
    }
    return ret;
}
