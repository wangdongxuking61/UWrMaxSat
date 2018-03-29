/*****************************************************************************[Hardware_sorters.cc]
Copyright (c) 2017-2018, Marek Piotrów, Michał Karpiński

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

#include "Hardware.h"

void encodeBySorter(vec<Formula>& vars, int max_sel, int ineq);
void encodeByMerger(const vec<Formula>& in1, const vec<Formula>& in2, vec<Formula>& outvars, unsigned k, int ineq);

//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

macro Formula operator && (Formula f, Formula g)
{
    if      (f == _0_ || g == _0_) return _0_;
    else if (f == _1_)             return g;
    else if (g == _1_)             return f;
    else if (f ==  g )             return f;
    else if (f == ~g )             return _0_;

    if (g < f) swp(f, g);
    return opt_shared_fmls ? Bin_newS(op_And, f, g) : Bin_new(op_And, f, g);
}

macro Formula operator || (Formula f, Formula g) {
    return ~(~f && ~g); }

static void oddEvenSelect(vec<Formula>& vars, unsigned k, int ineq);
static void splitAndSortSubsequences(vec<Formula>& vars, vec<int>& positions, unsigned k, int ineq);
static void oddEvenMerge(vec<Formula> const in[4], vec<Formula>& outvars, unsigned int k, int ineq);
static void oddEvenCombine(const vec<Formula>& x, const vec<Formula>& y, vec<Formula>& outvars, unsigned k);
static void oddEven4Combine(vec<Formula> const& x, vec<Formula> const& y, vec<Formula>& outvars, unsigned k);

static inline bool preferDirectMerge(unsigned n, unsigned k);
static void directMerge(const vec<Formula>& in1, const vec<Formula>& in2, 
                    vec<Formula>& outvars, unsigned k, int ineq);
static void directSort(vec<Formula>& vars, unsigned k, int ineq);
static void directCardClauses(const vec<Formula>& invars, unsigned start, 
                     unsigned pos, unsigned j, vec<Formula>& args, int ineq);

//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

void encodeBySorter(vec<Formula>& vars, int max_sel, int ineq)
{
    int k = opt_shared_fmls || max_sel < 0 || max_sel >= vars.size() ? vars.size() : max_sel;

    oddEvenSelect(vars, k, ineq);
}

void encodeByMerger(const vec<Formula>& in1, const vec<Formula>& in2, vec<Formula>& outvars, unsigned k, int ineq)
{
    int n = in1.size() + in2.size();
    vec<Formula> invars[4];

    if (ineq != 0 && preferDirectMerge(n,k))
        directMerge(in1, in2, outvars, k, ineq);
    else {
        if (in1.size() >= in2.size()) { in1.copyTo(invars[0]); in2.copyTo(invars[1]); }
        else                          { in1.copyTo(invars[1]); in2.copyTo(invars[0]); }
        oddEvenMerge(invars, outvars, k, ineq);
    }
 }
 
//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

static void oddEvenSelect(vec<Formula>& vars, unsigned k, int ineq)
{
    int n = vars.size();

    if ((int)k > n) k = n;
    if (k == 0) { vars.clear(); return; }
    if (k == 1) { directSort(vars, k, ineq); return; }

    vec<int> positions;

    splitAndSortSubsequences(vars, positions, k, ineq);

    if (positions.size() > 2) {
        // in loop: merge each 4 (or less) consequtive subsequences into one and select at most k largest items until one subsequence remains
        for (int seq_to_merge = positions.size() - 1; seq_to_merge > 1; seq_to_merge = (seq_to_merge+3)/4) {
            int step = 4, next = 0;
            for (int i = 0; i < seq_to_merge; i += step) {
                vec<Formula> invars[4], outvars;
                int tlength = 0;
                if (seq_to_merge - i == 5 /*|| seq_to_merge - i == 6*/) step = 3;
                for (int j = 0; j < min(step, seq_to_merge - i); j++) {
                    for (int p = positions[i+j], len = min((int)k, positions[i+j+1] - p); len > 0; p++, len--) 
                        invars[j].push(vars[p]);
                    tlength += invars[j].size();
                }
                if (ineq != 0 && preferDirectMerge(tlength, k)) {
                    if (invars[2].size() > 0) {
                        vec<Formula> out1,out2;
                        directMerge(invars[0], invars[1], out1, k, ineq);
                        directMerge(invars[2], invars[3], out2, k, ineq);
                        directMerge(out1, out2, outvars, k, ineq);
                    } else 
                        directMerge(invars[0], invars[1], outvars, k, ineq);
                } else 
		    oddEvenMerge(invars, outvars, k, ineq);
                for (int p = positions[i], len = min((int)k, outvars.size()), j = 0; j < len; j++, p++) 
                    vars[p] = outvars[j];
                positions[next++] = positions[i]; 
            }
            positions[next] = n;
        }
    }
    vars.shrink(vars.size() - k);
}

static void splitAndSortSubsequences(vec<Formula>& vars, vec<int>& positions, unsigned k, int ineq)
{
    int n = vars.size(), max_len = 0;
    int dir_sort_size = k <= 2 ? 7 : 5;

    vec<Formula> tmp, singles;
    positions.push(0); // split input vars into subsequenses of the same literal or sorted 5 singletons 
    for (int last = 0, i=1; i <= n; i++)
        if (i == n || vars[i] != vars[i-1]) {
            int len = i - last, tmp_sz = tmp.size() ;
            if (len > 1) { for (int j=last; j < i; j++) tmp.push(vars[j]); positions.push(tmp.size()); }
            else singles.push(vars[i-1]);
            if (singles.size() == dir_sort_size || i == n && singles.size() > 0) {
                directSort(singles, k, ineq);
                for (int j=0; j < singles.size(); j++) tmp.push(singles[j]);
                positions.push(tmp.size());
                singles.clear();
            } 
            max_len = max(max_len, tmp.size() - tmp_sz);
            last = i;
        }
    if (positions.size() == 2) { vars.clear(); tmp.copyTo(vars); } 
    else { // sort (by counting) vars with respect to the sizes of the subsequences in decreasing order
        vec<int> len_count(max_len+1, 0), start_pos(max_len+1, 0);

        for (int i = positions.size()-1; i > 0; i--) len_count[positions[i] - positions[i-1]]++;
        for (int i = max_len; i > 1; i--) start_pos[i-1] = start_pos[i] + len_count[i] * i;
        for (int i = 1; i < positions.size(); i++) // copy literals from tmp to correct positions
            for (int p = positions[i-1], len = positions[i] - p, j = 0; j < len; j++) vars[start_pos[len]++] = tmp[p++];
        for (int i = 1, len = max_len; len > 0; len--) // set new start positions of the subsequences
            for (int cnt = len_count[len]; cnt > 0; cnt--, i++) positions[i] = positions[i-1] + len; 
    }
}

static void oddEvenMerge(vec<Formula> const in[4], vec<Formula>& outvars, unsigned int in_k, int ineq) {
    int n = in[0].size() + in[1].size() + in[2].size() + in[3].size(), k = min((int)in_k, n);
    int nn[4] = { min(k, in[0].size()), min(k, in[1].size()), min(k, in[2].size()), min(k, in[3].size()) };    
    assert(nn[0] > 0); assert(nn[0] >= nn[1]); assert(nn[1] >= nn[2]); assert(nn[2] >= nn[3]);
    
    if (nn[1] == 0) {
        for (int i = 0 ; i < nn[0] ; i++) outvars.push(in[0][i]);
	return;
    }
    if (nn[0] == 1) {
        for (int i = 0; i < 4; i++)
            if (nn[i] > 0) outvars.push(in[i][0]);
        directSort(outvars, k, ineq); 
        return;
    }
    // from now on: nn[0] > 1 && nn[1] > 0 
    vec<Formula> even_odd[2][4], x, y;
    // split into odds and evens
    for (int i = 0; i < 4; i++)
        for (int j = 0; j < nn[i]; j++)
            even_odd[j % 2][i].push(in[i][j]);
    
    // recursive merges
    oddEvenMerge(even_odd[0], x, k/2+2,ineq);
    oddEvenMerge(even_odd[1], y, k/2,  ineq);
    
    // combine results
    if (nn[2] > 0)
        oddEven4Combine(x,y,outvars,k);
    else
        oddEvenCombine(x,y,outvars,k);
}

static void oddEvenCombine(const vec<Formula>& x, const vec<Formula>& y, vec<Formula>& outvars, unsigned k) {
    unsigned a = x.size(), b = y.size();
    if (k > a+b) k = a+b;   
    // both x and y are sorted and the numbers of ones in them satisfy: ones(y) <= ones(x) <= ones(y)+2
    outvars.push(x[0]);
    for (unsigned i = 0 ; i < (k-1)/2 ; i++) { // zip x with y and use a row of comparators: y[i] : x[i+1], i = 0,...
        outvars.push(y[i] | x[i+1]);
	outvars.push(y[i] & x[i+1]);
    }
    // set outvars[k-1] if k is even
    if (k % 2 == 0)
        outvars.push(k < a + b ? y[k/2-1] | x[k/2] : a == b ? y[k/2-1] : x[k/2]);
}
    
static void oddEven4Combine(vec<Formula> const& x, vec<Formula> const& y, 
                           vec<Formula>& outvars, unsigned k) {
    unsigned a = x.size(), b = y.size();
    assert(a >= b); assert(a <= b+4); assert(a >= 2); assert(b >= 1); 
    if (k > a+b) k = a+b;   
    // both x and y are sorted and the numbers of ones in them satisfy: ones(y) <= ones(x) <= ones(y)+4 
    outvars.push(x[0]);
    unsigned last = (k < a+b || k % 2 == 1 || a == b+2 ? k : k-1);
    for (unsigned i = 0, j = 1 ; j < last ; j++,i=j/2) { // zip x with y and use two rows of comparators: first y[i] : x[i+2], then y[i] : x[i+1] 
	Formula ret = _0_;
        if (j %2 == 0) { // new x[i] = min( max(y[i-1], x[i+1]), min(y[i-2], x[i]) ) = y[i-1] && x[i] || y[i-2] && x[i+1]
	    if (i+1 < a && i < b+2) ret = ret || x[i+1] && (i >= 2 ? y[i-2] : _1_);
            if (i < a && i < b+1)   ret = ret || x[i] && y[i-1];
        } else {  // new y[i] = max( max(y[i], x[i+2]), min(y[i-1], x[i+1]) ) = y[i] || x[i+2] || y[i-1] && x[i+1]
            if (i > 0 && i+2 < a)   ret = ret || x[i+2];
            if (i < b)              ret = ret || y[i];
            if (i+1 < a && i < b+1) ret = ret || x[i+1] && (i >= 1 ? y[i-1] : _1_);
        }
        outvars.push(ret);

    }
    if (k % 2 == 0 && k == a+b && a != b+2)
        outvars.push(a == b ? y[b-1] : x[a-1]);
}

static inline bool preferDirectMerge(unsigned n, unsigned k) {
    static unsigned minTest = 94, maxTest = 201;
    static unsigned short nBound[] = {
#include "DirOrOddEvenMerge.inl"
    } ;
    return k < minTest ? true : (k > maxTest ? false : (n < nBound[k-minTest]));
}

static void directMerge(const vec<Formula>& in1, const vec<Formula>& in2,vec<Formula>& outvars, unsigned k, int ineq) {
    // k is the desired size of sorted output; 1s (if ineq < ) or 0s (else) will be propagated from inputs to outputs.
    assert(outvars.size() == 0);
  
    int n = in1.size(), m = in2.size(), c = min(n+m,(int)k), a = min(n,c), b = min(m,c);

    if (b == 0)
        for (int i=0 ; i < c ; i++) outvars.push(in1[i]);
    else if (a == 0)
        for (int i=0 ; i < c ; i++) outvars.push(in2[i]);
    else if (ineq < 0) {
        for (int i=0 ; i < c ; i++) outvars.push(_0_);
        for (int i=0 ; i < a ; i++) outvars[i] |= in1[i];
        for (int i=0 ; i < b ; i++) outvars[i] |= in2[i];
        for (int j=0 ; j < b ; j++)
            for(int i=0 ; i < min(a,c-j-1) ; i++) outvars[i+j+1] |= in1[i] && in2[j];
    } else {
        for (int i=0 ; i < c ; i++) outvars.push(_1_);
        for (int i=0 ; i < min(a,c-m) ; i++) outvars[i+m] &= in1[i];
        for (int i=0 ; i < min(b,c-n) ; i++) outvars[i+n] &= in2[i];
        for (int j=0 ; j < b ; j++)
            for(int i=0 ; i < min(a,c-j) ; i++) outvars[i+j] &= in1[i] || in2[j];
    }
}

static void directSort(vec<Formula>& vars, unsigned k, int ineq) {
    unsigned n = vars.size();
   
    if (k > n) k = n;
    vec<Formula> invars; vars.copyTo(invars);
    if (ineq <= 0) {
        for (unsigned j=1 ; j <= k ; j++) {
            vec<Formula> args;
            for (unsigned i=0 ; i < j; i++) args.push(_1_);
            args.push(_0_);
            directCardClauses(invars, 0, 0, j, args, ineq); //vars[j-1] := \/ (1<= i1 < .. <ij <= n) /\ (s=1..j) invars[is]
            vars[j-1] = args[j];
        }
    } else {
        for (unsigned j=n ; j > n-k ; j--) {
            vec<Formula> args;
            for (unsigned i=0 ; i < j; i++) args.push(_0_);
            args.push(_1_);
            directCardClauses(invars, 0, 0, j, args, ineq); // outvars[j-1] := /\ (1<= i1 < .. <ij <= n) \/ (s=1..j) invars[is]
            vars[n-j] = args[j];
        }
    }
    vars.shrink(n-k);
}

static void directCardClauses(const vec<Formula>& invars, unsigned start, unsigned pos, unsigned j, vec<Formula>& args, int ineq) {
    // 1s will be propagated from inputs to outputs if ineq < 0; 0s - otherwise.
    unsigned n = invars.size();
    if (pos == j) {
        if (ineq < 0) {
            Formula conj = _1_;
            for (unsigned i=0 ; i < j ; i++) conj = conj && args[i];
            args[j] = args[j] | conj;
        } else {
            Formula disj = _0_;
            for (unsigned i=0 ; i < j ; i++) disj = disj || args[i];
            args[j] = args[j] & disj;
        }
    } else
        for (unsigned i = start ; i <= n - (j - pos) ; i++) {
	    args[pos] = invars[i];
	    directCardClauses(invars, i+1, pos+1, j, args, ineq);
        }
}
