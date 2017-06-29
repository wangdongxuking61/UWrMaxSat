/*****************************************************************************[Hardware_sorters.cc]
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

#include "Hardware.h"

//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

macro Formula operator && (Formula f, Formula g)
{
    if      (f == _0_ || g == _0_) return _0_;
    else if (f == _1_)             return g;
    else if (g == _1_)             return f;
    else if (f ==  g )             return f;
    else if (f == ~g )             return _0_;

    if (g < f) swp(f, g);
    return Bin_new(op_And, f, g);
}

macro Formula operator || (Formula f, Formula g) {
    return ~(~f && ~g); }

//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -


static inline void cmp2(vec<Formula>& fs, int begin)
{
    Formula a     = fs[begin];
    Formula b     = fs[begin + 1];
#if 1
    fs[begin]     = a | b;
    fs[begin + 1] = a & b;
#else
    fs[begin]     = a || b;
    fs[begin + 1] = a && b;
#endif
}

static void riffle(vec<Formula>& fs)
{
    vec<Formula> tmp; fs.copyTo(tmp);
    for (int i = 0; i < fs.size() / 2; i++){
        fs[i*2]   = tmp[i];
        fs[i*2+1] = tmp[i+fs.size() / 2];
    }
}

static void unriffle(vec<Formula>& fs)
{
    vec<Formula> tmp; fs.copyTo(tmp);
    for (int i = 0; i < fs.size() / 2; i++){
        fs[i]               = tmp[i*2];
        fs[i+fs.size() / 2] = tmp[i*2+1];
    }
}

static void oddEvenMerge(vec<Formula>& fs, int begin, int end)
{
    assert(end - begin > 1);
    if (end - begin == 2)
        cmp2(fs,begin);
    else {
        int          mid = (end - begin) / 2;
        vec<Formula> tmp;
        for (int i = 0; i < end - begin; i++)
            tmp.push(fs[begin+i]);
        unriffle(tmp);
        oddEvenMerge(tmp,0,mid);
        oddEvenMerge(tmp,mid,tmp.size());
        riffle(tmp);
        for (int i = 1; i < tmp.size() - 1; i += 2)
            cmp2(tmp,i);
        for (int i = 0; i < tmp.size(); i++)
            fs[i + begin] = tmp[i];
    }
}

// Inputs to the circuit is the formulas in fs, which is overwritten
// by the resulting outputs of the circuit.
// NOTE: The number of comparisons is bounded by: n * log n * (log n + 1)
static void oldOddEvenSort(vec<Formula>& fs)
{
    int orig_sz = fs.size();
    int sz; for (sz = 1; sz < fs.size(); sz *= 2);
    fs.growTo(sz,_0_);

    for (int i = 1; i < fs.size(); i *= 2)
        for (int j = 0; j + 2*i <= fs.size(); j += 2*i)
            oddEvenMerge(fs,j,j+2*i);
    fs.shrink(sz - orig_sz);
}


void oddEvenSort(vec<Formula>& vars, int max_sel, int ineq);

static inline bool preferDirectMerge(unsigned n, unsigned k);
static inline void sort2(Formula& a, Formula& b); // comparator

static void DirectCardClauses(const vec<Formula>& invars, unsigned start, 
                     unsigned pos, unsigned j, vec<Formula>& args, int ineq);
static void DirectSort(vec<Formula>& vars, unsigned k, int ineq);
static void DirectMerge(const vec<Formula>& in1, const vec<Formula>& in2, 
                    vec<Formula>& outvars, unsigned k, int ineq);

static void OddEvenSelect(vec<Formula>& vars, unsigned k,int ineq);
static void OddEvenCombine(const vec<Formula>& in1, const vec<Formula>& in2, 
                    vec<Formula>& outvars, unsigned k);
static void OddEvenMerge(const vec<Formula>& in1,  const vec<Formula>& in2, 
                    vec<Formula>& outvars, unsigned k);

static void modifiedOddEvenSort(vec<Formula>& vars, int ineq);
static void columnSort(vec<Formula>& vars, int ineq);
//static bool directOddEvenSelect(const vec<Formula>& invars, vec<Formula>& outvars, 
//                    unsigned k, int ineq);

static void OddEven4Select(vec<Formula>& vars, unsigned k, int ineq);
static void OddEven4Combine(vec<Formula> const& x, vec<Formula> const& y, 
                    vec<Formula>& outvars, unsigned k);
static void OddEven4Merge(vec<Formula> const& a, vec<Formula> const& b, vec<Formula> const& c, 
                    vec<Formula> const& d, vec<Formula>& outvars, unsigned int k, int ineq);

void oddEvenSort(vec<Formula>& vars, int max_sel, int ineq)
{
    int k = max_sel < 0 || max_sel >= vars.size() ? vars.size() : max_sel;
    switch (opt_sort_alg) {
        case 1: oldOddEvenSort(vars); break;
        case 3: //columnSort(vars, ineq); break;
                modifiedOddEvenSort(vars, ineq); break;
        /*{   vec<Formula> outvars;
            if (ineq != 0 && directOddEvenSelect(vars, outvars, k, ineq)) {
                outvars.copyTo(vars);
                break;
            }
        }*/
        case 2: OddEvenSelect(vars, k, ineq);  break;
        case 4: OddEven4Select(vars, k, ineq); break;
    }  
    
}

static inline unsigned pow2roundup (unsigned x) {
    if(x == 0) return 0;
    --x;
    x |= x >> 1;
    x |= x >> 2;
    x |= x >> 4;
    x |= x >> 8;
    x |= x >> 16;
    return x+1;
}

static inline bool preferDirectMerge(unsigned n, unsigned k) {
    static unsigned minTest = 94, maxTest = 201;
    static unsigned short nBound[] = {
#include "DirOrOddEvenMerge.inl"
  } ;
  return k < minTest ? true : (k > maxTest ? false : (n < nBound[k-minTest]));
}

static inline void sort2(Formula& a, Formula& b) // comparator
{
    Formula x = a, y = b;
    a = x | y;
    b = x & y;
}

static void DirectCardClauses(const vec<Formula>& invars, unsigned start, unsigned pos, unsigned j, vec<Formula>& args, int ineq) {
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
  } else {
    for (unsigned i = start ; i <= n - (j - pos) ; i++) {
	      args[pos] = invars[i];
	      DirectCardClauses(invars, i+1, pos+1, j, args, ineq);
    }
  }  
}

static void DirectSort(vec<Formula>& vars, unsigned k, int ineq) {
  unsigned n = vars.size();
   
  if (k > n) k = n;
  bool same = true;
  for (unsigned i=1; i < n && same; i++)
      if (vars[i] != vars[0]) same = false;
  if (!same) { 
    vec<Formula> invars; vars.copyTo(invars);
    if (ineq < 0) {
        for (unsigned j=1 ; j <= k ; j++) {
            vec<Formula> args;
            for (unsigned i=0 ; i < j; i++) args.push(_1_);
            args.push(_0_);
            DirectCardClauses(invars, 0, 0, j, args, ineq); //vars[j-1] := \/ (1<= i1 < .. <ij <= n) /\ (s=1..j) invars[is]
            vars[j-1] = args[j];
        }
    } else {
        for (unsigned j=n ; j > n-k ; j--) {
            vec<Formula> args;
            for (unsigned i=0 ; i < j; i++) args.push(_0_);
            args.push(_1_);
            DirectCardClauses(invars, 0, 0, j, args, ineq); // outvars[j-1] := /\ (1<= i1 < .. <ij <= n) \/ (s=1..j) invars[is]
            vars[n-j] = args[j];
        }
    }
  }
  vars.shrink(n-k);
  return;
}

static void DirectMerge(const vec<Formula>& in1, const vec<Formula>& in2,vec<Formula>& outvars, unsigned k, int ineq) {
  // k is the desired size of sorted output; 1s (if ineq < ) or 0s (else will be propagated from inputs to outputs.
  assert(outvars.empty());
  
  unsigned n = in1.size(), m = in2.size(), c = min(n+m,k), a = min(n,c), b = min(m,c);

  if (b == 0)
    for (unsigned i=0 ; i < c ; i++) outvars.push(in1[i]);
  else if (a == 0)
    for (unsigned i=0 ; i < c ; i++) outvars.push(in2[i]);
  else if (ineq < 0) {
    for (unsigned i=0 ; i < c ; i++) outvars.push(_0_);
    for (unsigned i=0 ; i < a ; i++) outvars[i] |= in1[i];
    for (unsigned i=0 ; i < b ; i++) outvars[i] |= in2[i];
    for (unsigned j=0 ; j < b ; j++)
      for(unsigned i=0 ; i < min(a,c-j-1) ; i++) outvars[i+j+1] |= in1[i] && in2[j];
  } else {
    for (unsigned i=0 ; i < c ; i++) outvars.push(_1_);
    for (unsigned i=0 ; i < min(a,c-m) ; i++) outvars[i+m] &= in1[i];
    for (unsigned i=0 ; i < min(b,c-n) ; i++) outvars[i+n] &= in2[i];
    for (unsigned j=0 ; j < b ; j++)
      for(unsigned i=0 ; i < min(a,c-j) ; i++) outvars[i+j] &= in1[i] || in2[j];
  }
}

static void OddEvenSelect(vec<Formula>& vars, unsigned k, int ineq) {
  unsigned n = vars.size();

  assert(k <= n);

  if (n <= 1) {
      if (k == 0) vars.clear();
      else vars.shrink(n-k);
      return;
  }
  //if (ineq < 0 && (k==1 || k==2 && n <= 39 || k==3 && n <= 10 || k==4 && n <= 8 || n<=6) ||
  //    ineq > 0 && (k==1 || k==2 && n <= 11 || k==3 && n <=  9 || k==4 && n <= 7 || n<=6)    ) {
  if (ineq < 0 && (k == 1 || k == 2 && n <= 8 || n <= 6) ||
      ineq > 0 && (k == 1 || k == 2 && n <= 7 || n <= 5)    ) {
       DirectSort(vars, k, ineq);
       return;
  }

  unsigned n1, n2;
  unsigned p2 = (k==2 ? 1 : pow2roundup((k+4)/3));
  n2 = (n <= 7 ? n/2 : abs((int)k/2-p2) > (k+3)/4 ? (k <= n/2 ? k : k/2) : (2*p2 <= n/2 ? 2*p2 : p2) );
  n1 = n - n2;

  // split
  vec<Formula> x, y;
  for (unsigned i=0; i < n1; i++) x.push(vars[i]);
  for (unsigned i=n1; i < n; i++) y.push(vars[i]);

  // recursive calls
  OddEvenSelect(x, min(k, n1), ineq);
  OddEvenSelect(y, min(k, n2), ineq);

  // merging
  vars.clear();
  if (ineq != 0 && preferDirectMerge(n,k))
      DirectMerge(x, y, vars, k, ineq);
  else
      OddEvenMerge(x, y, vars, k);
}


static void OddEvenCombine(const vec<Formula>& in1, const vec<Formula>& in2, vec<Formula>& outvars, unsigned k) {
    unsigned a = in1.size(), b = in2.size();
    if (k > a+b) k = a+b;   
 
    // set outvars[0] = in1[0];
    outvars.push(in1[0]);

    for (unsigned i = 0 ; i < (k-1)/2 ; i++) {
        outvars.push(in2[i]); outvars.push(in1[i+1]);
        sort2(outvars[i*2+1], outvars[i*2+2]);
    }

    // set outvars[k-1] if k is even
    if (k % 2 == 0)
        if (k < a + b)   outvars.push(in1[k/2] | in2[k/2-1]);
        else if (a == b) outvars.push(in2[k/2-1]);
        else             outvars.push(in1[k/2]);
}
    
static void OddEvenMerge(const vec<Formula>& in1, const vec<Formula>& in2, vec<Formula>& outvars, unsigned k) {
    unsigned a = in1.size(), b = in2.size();
    
    if (a+b < k) k = a+b;
    if (a > k) a = k;
    if (b > k) b = k;
    if (a == 0) {
        for (unsigned i = 0 ; i < b ; i++) outvars.push(in2[i]);
	return;
    }
    if (b == 0) {
        for (unsigned i = 0 ; i < a ; i++) outvars.push(in1[i]);
	return;
    }
    if (a == 1 && b == 1) {
      if (k == 1) outvars.push(in1[0] | in2[0]);
      else { // k == 2
        outvars.push(in1[0]); outvars.push(in2[0]);
        sort2(outvars[0], outvars[1]);
      }
      return;
    }
    // from now on: a > 0 && b > 0 && && a,b <= k && 1 < k <= a + b 
    
    vec<Formula> in1odds, in2odds, in1evens, in2evens, tmp1, tmp2;
    // in1evens = in1[0,2,4,...], in2evens same
    // in1odds  = in1[1,3,5,...], in2odds same
    for (unsigned i = 0 ; i < a; i+=2) {
        in1evens.push(in1[i]);
        if (i + 1 < a) in1odds.push(in1[i+1]);
    }
    for (unsigned i = 0 ; i < b; i+=2) {
        in2evens.push(in2[i]);
        if (i + 1 < b) in2odds.push(in2[i+1]);
    }
    OddEvenMerge(in1evens, in2evens, tmp1, k/2+1);
    OddEvenMerge(in1odds, in2odds, tmp2, k/2);
    OddEvenCombine(tmp1,tmp2,outvars,k);
}

static void OddEven4Select(vec<Formula>& vars, unsigned k, int ineq) {
  unsigned n = vars.size();

  assert(k <= n);
  if (n <= 1) {
    if (k == 0) vars.clear();
    else vars.shrink(n-k);
    return;
  }
 
  if (ineq < 0 && (k == 1 || k == 2 && n <= 8 || n <= 6) ||
      ineq > 0 && (k == 1 || k == 2 && n <= 7 || n <= 5)    ) {
    DirectSort(vars, k, ineq);
    return;
  }
  // select sizes
  unsigned n1, n2, n3, n4;
  if (n <= 7) { 
    n4=n/4; n3=(n+1)/4; n2=(n+2)/4; 
  } else {
    int p2 = (k/2==2 ? 1 : pow2roundup((k/2+4)/3));
    n4 = (abs((int)k/4-p2) > ((int)k/2+3)/4 || 4*p2 > (int)n ? k/4 : p2);
    n3 = (n == k && n4 == k/4 ? (k+1)/4 : n4);
    n2 = (n == k && n4 == k/4 ? (k+2)/4 : n4);
  }
  n1 = n - n2 - n3 - n4;
  
  // split
  vec<Formula> a, b, c, d;
  for (unsigned i=0; i < n1; i++) a.push(vars[i]);
  for (unsigned i=0; i < n2; i++) b.push(vars[n1+i]);
  for (unsigned i=0; i < n3; i++) c.push(vars[n1+n2+i]);
  for (unsigned i=0; i < n4; i++) d.push(vars[n1+n2+n3+i]);
  
  // recursive calls
  unsigned k1 = min(k, n1), k2 = min(k, n2), k3 = min(k, n3), k4 = min(k, n4);
  OddEven4Select(a, k1,ineq);
  OddEven4Select(b, k2,ineq);
  OddEven4Select(c, k3,ineq);
  OddEven4Select(d, k4,ineq);

  // merging
  vars.clear();
  if (ineq != 0 && preferDirectMerge(n,k)) {
      vec<Formula> out1,out2;
      DirectMerge(a, b, out1, min(k1+k2,k), ineq);
      DirectMerge(c, d, out2, min(k3+k4,k), ineq);
      DirectMerge(out1, out2, vars, k, ineq);
  } else {
      OddEven4Merge(a, b, c, d, vars, k, ineq);
    //  vec<Formula> out1,out2;
    //  OddEvenMerge(a, b, out1, min(k1+k2, k));
    //  OddEvenMerge(c, d, out2, min(k3+k4, k));
    //  OddEvenMerge(out1, out2, vars,k);

  } 
}

static void OddEven4Combine(vec<Formula> const& x, vec<Formula> const& y, 
                           vec<Formula>& outvars, unsigned k) {
    unsigned a = x.size(), b = y.size();
    assert(a >= b); assert(a <= b+4); assert(a >= 2); assert(b >= 1); 
    if (k > a+b) k = a+b;   

    // set outvars[0] = x[0];
    outvars.push(x[0]);
    unsigned last = (k < a+b || k % 2 == 1 || a == b+2 ? k : k-1);
    for (unsigned i = 0, j = 1 ; j < last ; j++,i=j/2) {
	Formula ret = _0_;
        if (j %2 == 0) {
	    if (i+1 < a && i < b+2) ret = ret || x[i+1] && (i >= 2 ? y[i-2] : _1_);
            if (i < a && i < b+1)   ret = ret || x[i] && y[i-1];
        } else {
            if (i > 0 && i+2 < a)   ret = ret || x[i+2];
            if (i < b)              ret = ret || y[i];
            if (i+1 < a && i < b+1) ret = ret || x[i+1] && (i >= 1 ? y[i-1] : _1_);
        }
        outvars.push(ret);

    }
    if (k == a+b && k % 2 == 0 && a != b+2)
        if (a == b) outvars.push(y[b-1]);
        else outvars.push(x[a-1]);
}
    
static void OddEven4Merge(vec<Formula> const& a, vec<Formula> const& b, vec<Formula> const& c, 
                    vec<Formula> const& d, vec<Formula>& outvars, unsigned int k, int ineq) {
    unsigned na = a.size(), nb = b.size(), nc = c.size(), nd = d.size();

    assert(na > 0); assert(na >= nb); assert(nb >= nc); assert(nc >= nd);
    if (na+nb+nc+nd < k) k = na+nb+nc+nd;
    if (na > k) na = k;
    if (nb > k) nb = k;
    if (nc > k) nc = k;
    if (nd > k) nd = k;
    
    if (nb == 0) {
        for (unsigned i = 0 ; i < na ; i++) outvars.push(a[i]);
	return;
    }
    if (na == 1) {
        outvars.push(a[0]); outvars.push(b[0]);
        if (nc > 0) outvars.push(c[0]);
        if (nd > 0) outvars.push(d[0]);
        if (ineq != 0)     DirectSort(outvars, k, ineq); 
        else               OddEvenSelect(outvars, k, ineq);
        return;
    }
    // from now on: na > 1 && nb > 0 
    vec<Formula> aodds, aevens, bodds, bevens, codds, cevens, dodds, devens, x, y;
    // split into odds and evens
    for (unsigned i = 0 ; i < na; i+=2) {
        aevens.push(a[i]);
        if (i + 1 < na) aodds.push(a[i+1]);
    }
    for (unsigned i = 0 ; i < nb; i+=2) {
        bevens.push(b[i]);
        if (i + 1 < nb) bodds.push(b[i+1]);
    }
    for (unsigned i = 0 ; i < nc; i+=2) {
        cevens.push(c[i]);
        if (i + 1 < nc) codds.push(c[i+1]);
    }
    for (unsigned i = 0 ; i < nd; i+=2) {
        devens.push(d[i]);
        if (i + 1 < nd) dodds.push(d[i+1]);
    }
    
    // recursive merges
    OddEven4Merge(aevens, bevens, cevens, devens, x, k/2+2,ineq);
    OddEven4Merge(aodds, bodds, codds, dodds, y, k/2,ineq);
    
    // combine results
    OddEven4Combine(x,y,outvars,k);
}

static void modifiedOddEvenMerge(vec<Formula>& fs, int begin, int end, int ineq)
{
    int n = end - begin, mid = n/2;
    vec<Formula> tmp;
    assert(n > 1);
   
    if (ineq == 0) {
        oddEvenMerge(fs, begin, end);
        return;
    }
    if (n <= 4) {
        for (int i = 0; i < n; i++) tmp.push(fs[begin+i]);
        DirectSort(tmp, n, ineq);
    } else if (n <= 128) {
        vec<Formula> tmp1, tmp2;
        for (int i = 0; i < mid; i++) tmp1.push(fs[i + begin]);
        for (int i = mid; i < n; i++) tmp2.push(fs[i + begin]);
        DirectMerge(tmp1, tmp2, tmp, n, ineq);
    } else {
        for (int i = 0; i < n; i++) tmp.push(fs[begin+i]);
        unriffle(tmp);
        modifiedOddEvenMerge(tmp, 0, mid, ineq);
        modifiedOddEvenMerge(tmp, mid, n, ineq);
        riffle(tmp);
        for (int i = 1; i < n - 1; i += 2)
            cmp2(tmp,i);
    }
    for (int i = 0; i < n; i++) fs[i + begin] = tmp[i];
}

// Inputs to the circuit is the formulas in fs, which is overwritten
// by the resulting outputs of the circuit.
// NOTE: The number of comparisons is bounded by: n * log n * (log n + 1)
static void modifiedOddEvenSort(vec<Formula>& fs, int ineq)
{
    int orig_sz = fs.size();
    int sz; for (sz = 1; sz < fs.size(); sz *= 2);
    fs.growTo(sz,_0_);

    for (int i = 1; i < fs.size(); i *= 2)
        for (int j = 0; j + 2*i <= fs.size(); j += 2*i)
            modifiedOddEvenMerge(fs, j, j+2*i, ineq);
    fs.shrink(sz - orig_sz); 
}

#if 0
// a version of OddEvenSelect with direct generation of clauses
#include "minisat/simp/SimpSolver.h"
#include "PbSolver.h"

extern PbSolver *pb_solver;
static SimpSolver *S = NULL;

#define lit2fml(p) id(var(var(p)),sign(p))

static void dirDirectSort(const vec<Formula>& invars, vec<Formula>& outvars, unsigned k, int ineq);
static void dirDirectCardClauses(const vec<Lit>& in, unsigned start, unsigned pos, unsigned j, 
                                   Minisat::vec<Lit>& args, int ineq);

static void dirDirectMerge(const vec<Formula>& in1, const vec<Formula>& in2, 
                    vec<Formula>& outvars, unsigned k, int ineq);

static void dirOddEvenSelect(const vec<Formula>& invars, vec<Formula>& outvars, 
                    unsigned k, int ineq);
static void dirOddEvenCombine(const vec<Formula>& in1, const vec<Formula>& in2, 
                    vec<Formula>& outvars, unsigned k, int ineq);
static void dirOddEvenMerge(const vec<Formula>& in1,  const vec<Formula>& in2, 
                    vec<Formula>& outvars, unsigned k, int ineq);


static bool directOddEvenSelect(const vec<Formula>& invars, vec<Formula>& outvars, unsigned k, int ineq) {
    for (int i=0; i < invars.size(); i++)
        if (!Atom_p(invars[i])) return false;
    S = &pb_solver->sat_solver;
    
    dirOddEvenSelect(invars, outvars, k, ineq);
    
/*    Lit last = Minisat::lit_Error;
    for (int i = outvars.size()-1; i > 0; i--)
        if (outvars[i] != _1_ && outvars[i] != _0_) {
            Lit act = mkLit(index(outvars[i]),sign(outvars[i]));
            if (last != Minisat::lit_Error) S->addClause(~last, act);
            last = act;
        } */
    return true;
}

static void dirOddEvenSelect(const vec<Formula>& invars, vec<Formula>& outvars, unsigned k,int ineq) {
  assert(outvars.empty());

  unsigned n = invars.size();

  assert(k <= n);

  /* if (k == 0) {
    for (unsigned i = 0 ; i < n ; i++) {
      if(invars[i] == _0_ || invars[i] == _1_) continue;
      S->addClause(~mkLit(index(invars[i]),sign(invars[i])));
    }
    return;
  } */

  if (n == 0 || k == 0) return;
  if (n == 1) {
    outvars.push(invars[0]);
    return;
  }

  if (ineq < 0 && (k==1 || k==2 && n <= 39 || k==3 && n <= 10 || k==4 && n <= 8 || n<=6)  ||
      ineq > 0 && (k==1 || k==2 && n <= 10 || k==3 && n <= 8 || k==4 && n <= 7 || n<=6)) {
       dirDirectSort(invars, outvars, k, ineq);
       return;
  }

  unsigned n1, n2;
  unsigned p2 = (k==2 ? 1 : pow2roundup((k+4)/3));
  n2 = (n <= 7 ? n/2 : abs((int)k/2-p2) > (k+3)/4 ? (k <= n/2 ? k : k/2) : (2*p2 <= n/2 ? 2*p2 : p2) );
  n1 = n - n2;

  // split
  vec<Formula> x, y;
  for (unsigned i=0; i < n1; i++) x.push(invars[i]);
  for (unsigned i=n1; i < n; i++) y.push(invars[i]);

  // recursive calls
  vec<Formula> _x, _y;
  dirOddEvenSelect(x, _x, min(k, n1), ineq);
  dirOddEvenSelect(y, _y, min(k, n2), ineq);

  // merging
  if (ineq != 0 && preferDirectMerge(n,k))
      //if (ineq < 0) DirectMergeLT(_x,_y,outvars,k);
      //else          DirectMergeGT(_x,_y,outvars,k);
      dirDirectMerge(_x,_y,outvars,k, ineq);
  else
      OddEvenMerge(_x, _y, outvars, k);
      // dirOddEvenMerge(_x, _y, outvars, k, ineq);

  return;
}

static void comparator(Formula &a, Formula &b, int ineq)
{
    if (a ==  b) return;
    Lit la = mkLit(index(a),sign(a)), lb = mkLit(index(b),sign(b)),
        c =  mkLit(S->newVar(l_Undef, !opt_branch_pbvars)),
        d =  mkLit(S->newVar(l_Undef, !opt_branch_pbvars));
    // 3-clause comparator,
    if (ineq <= 0 || !opt_convert_weak) {
        S->addClause(~la, c);      // a -> c
        S->addClause(~lb, c);      // b -> c
        S->addClause(~la, ~lb, d); // a & b -> d 
    }
    if (ineq >= 0 || !opt_convert_weak) {
        S->addClause(~c, la, lb);  // c -> a | b
        S->addClause(~d, la);      // d -> a
        S->addClause(~d, lb);      // d -> b
    }
    a = lit2fml(c); b = lit2fml(d);
}

static void halfcomparator(Formula &a, const Formula &b, int ineq)
{
    if (a ==  b) return;
    Lit la = mkLit(index(a),sign(a)), lb = mkLit(index(b),sign(b)),
        c = mkLit(S->newVar(l_Undef, !opt_branch_pbvars));
    if (ineq <= 0 || !opt_convert_weak) {
        S->addClause(~la,c);      // a -> c
        S->addClause(~lb,c);      // b -> c
    }
    if (ineq >= 0 || !opt_convert_weak)
        S->addClause(~c, la, lb);  // c -> a | b
    a = lit2fml(c);
}

static void dirOddEvenCombine(const vec<Formula>& in1, const vec<Formula>& in2, vec<Formula>& outvars, 
                              unsigned k, int ineq) {
    unsigned a = in1.size(), b = in2.size();
    if (k > a+b) k = a+b;   
 
    outvars.push(in1[0]);

    for (unsigned i = 0 ; i < (k-1)/2 ; i++) {
        outvars.push(in2[i]); outvars.push(in1[i+1]);
        sort2(outvars[i*2+1], outvars[i*2+2]);
        //comparator(outvars[i*2+1], outvars[i*2+2], ineq);
    }

    // set outvars[k-1] if k is even
    if (k % 2 == 0)
        if (k < a + b) {
            outvars.push(in1[k/2]);
            outvars[k-1] &= in2[k/2-1]; 
            //halfcomparator(outvars[k-1], in2[k/2-1], ineq);
        }
        else if (a == b) outvars.push(in2[k/2-1]);
        else             outvars.push(in1[k/2]);
}
   
static void dirOddEvenMerge(const vec<Formula>& in1, const vec<Formula>& in2, vec<Formula>& outvars, 
                            unsigned k, int ineq) {
    unsigned a = in1.size(), b = in2.size();
    
    if (a+b < k) k = a+b;
    if (a > k) a = k;
    if (b > k) b = k;
    if (a == 0) {
        for (unsigned i = 0 ; i < b ; i++) outvars.push(in2[i]);
	return;
    }
    if (b == 0) {
        for (unsigned i = 0 ; i < a ; i++) outvars.push(in1[i]);
	return;
    }
    if (a == 1 && b == 1) {
      if (k == 1) {
          outvars.push(in1[0]);
          outvars[0] &= in2[0];
          //halfcomparator(outvars[0],in2[0], ineq);
      } else { // k == 2
        outvars.push(in1[0]); outvars.push(in2[0]);
        sort2(outvars[0], outvars[1]);
        //comparator(outvars[0], outvars[1], ineq);
      }
      return;
    }
    // from now on: a > 0 && b > 0 && && a,b <= k && 1 < k <= a + b 
    
    vec<Formula> in1odds, in2odds, in1evens, in2evens, tmp1, tmp2;
    // in1evens = in1[0,2,4,...], in2evens same
    // in1odds  = in1[1,3,5,...], in2odds same
    for (unsigned i = 0 ; i < a; i+=2) {
        in1evens.push(in1[i]);
        if (i + 1 < a) in1odds.push(in1[i+1]);
    }
    for (unsigned i = 0 ; i < b; i+=2) {
        in2evens.push(in2[i]);
        if (i + 1 < b) in2odds.push(in2[i+1]);
    }
    dirOddEvenMerge(in1evens, in2evens, tmp1, k/2+1, ineq);
    dirOddEvenMerge(in1odds, in2odds, tmp2, k/2, ineq);
    dirOddEvenCombine(tmp1, tmp2, outvars, k, ineq);
}

static void dirDirectSort(const vec<Formula>& invars, vec<Formula>& outvars, unsigned k, int ineq) {
  assert(outvars.empty());
  unsigned n = invars.size();
  vec<Lit> in, out;
  
  if (k == 0) return;
  if (k > n) k = n;
  bool same = true;
  for (unsigned i=1; i < n && same; i++)
      if (invars[i] != invars[0]) same = false;
  if (same) { 
      for (unsigned i=0; i < k; i++) outvars.push(invars[i]);
      return; 
  }
  for (unsigned i=0 ; i < n ; i++) in.push(mkLit(index(invars[i]),sign(invars[i])));
  for (unsigned i=0 ; i < k ; i++) {
      Var x = S->newVar(l_Undef, !opt_branch_pbvars);
      Lit a = mkLit(x);
      out.push(a);
      outvars.push(lit2fml(a));
  }  
  if (ineq < 0) {
    for (unsigned j=1 ; j <= k ; j++) {
        Minisat::vec<Lit> args;
        for (unsigned i=0 ; i < j; i++) args.push(Minisat::lit_Error);
        args.push(out[j-1]);
        dirDirectCardClauses(in, 0, 0, j, args, ineq);
    }
  } else {
    for (unsigned j=n ; j > n-k ; j--) {
        Minisat::vec<Lit> args;
        for (unsigned i=0 ; i < j; i++) args.push(Minisat::lit_Error);
        args.push(~out[n-j]);
        dirDirectCardClauses(in, 0, 0, j, args, ineq);
    }
  }
}

static void dirDirectCardClauses(const vec<Lit>& in, unsigned start, unsigned pos, unsigned j, 
                                   Minisat::vec<Lit>& args, int ineq) {
  unsigned n = in.size();
  if (pos == j) {
    S->addClause(args);
  } else {
    for (unsigned i = start ; i <= n - (j - pos) ; i++) {
      args[pos] = (ineq < 0 ? ~in[i] : in[i]);
      dirDirectCardClauses(in, i+1, pos+1, j, args, ineq);
    }
  }  
}

static void dirDirectMerge(const vec<Formula>& in1, const vec<Formula>& in2,vec<Formula>& outvars, 
                           unsigned k, int ineq) {
  unsigned n = in1.size(), m = in2.size(), a = min(n, k), b = min(m, k), c = min(a+b, k);
  if (b == 0)
    for (unsigned i=0 ; i < c ; i++) outvars.push(in1[i]);
  else if (a == 0)
    for (unsigned i=0 ; i < c ; i++) outvars.push(in2[i]);
  else {
    vec<Lit> inlits1, inlits2, outlits;
      
    for (unsigned i=0 ; i < a ; i++) inlits1.push(mkLit(index(in1[i]),sign(in1[i])));
    for (unsigned i=0 ; i < b ; i++) inlits2.push(mkLit(index(in2[i]),sign(in2[i])));
    for (unsigned i=0 ; i < c ; i++) {
        Lit a = mkLit(S->newVar(l_Undef, !opt_branch_pbvars));
        outlits.push(a);
        outvars.push(lit2fml(a));
    }  
    if (ineq < 0) {
        for (unsigned i=0 ; i < a ; i++)
            S->addClause(~inlits1[i], outlits[i]);    // inlits1[i] -> outlits[i]
        for (unsigned i=0 ; i < b ; i++) 
            S->addClause(~inlits2[i], outlits[i]);    // inlits2[i] -> outlits[i]
        for (unsigned j=0 ; j < b ; j++)
            for(unsigned i=0 ; i < min(a,c-j-1) ; i++)// inlits1[i] & inlits2[j] -> outlits[i+j]
                S->addClause(~inlits1[i], ~inlits2[j], outlits[i+j+1]);
    } else {
        for (unsigned i=0 ; i < min(a,c-b) ; i++)
            S->addClause(inlits1[i], ~outlits[i+b]);  // outlits[i+b] -> inlits1[i]
        for (unsigned i=0 ; i < min(b,c-a) ; i++)
             S->addClause(inlits2[i], ~outlits[i+a]); // outlits[i+a] -> inlits1[i]
        for (unsigned j=0 ; j < b ; j++)              // outlits[i+j] -> inlits1[i] | inlits2[j]
          for(unsigned i=0 ; i < min(a,c-j) ; i++)
             S->addClause(inlits1[i], inlits2[j], ~outlits[i+j]);
    }
  }
}
#endif

static void rangeOddEvenSort(vec<Formula>& fs, int begin, int end, int ineq)
{
    int n = end - begin;

    for (int i = 1; i < n; i *= 2)
        for (int j = begin; j + 2*i <= end; j += 2*i)
            modifiedOddEvenMerge(fs, j, j+2*i, ineq);
}

static void transpose(vec<Formula>& fs, int s)
{
   vec<Formula> tmp; fs.copyTo(tmp);
   int n = fs.size(), r = n / s;
   
   for (int i = 0, j = 0; i < n; i++, j += r) {
       if (j >= n) j = j % r + 1;
       fs[j] = tmp[i];
   }
}

static void untranspose(vec<Formula>& fs, int s)
{
   vec<Formula> tmp; fs.copyTo(tmp);
   int n = fs.size(), r = n / s;
   
   for (int i = 0, j = 0; i < n; i++, j += r) {
       if (j >= n) j = j % r + 1;
       fs[i] = tmp[j];
   }
}

static void columnSort(vec<Formula>& fs, int ineq)
{
    int orig_sz = fs.size();

    if (orig_sz <= 64)
        modifiedOddEvenSort(fs, ineq);
    else {                                                  // ColumnSort algorithm by Leighton
        int n, lgn; for (n = 1, lgn = 0; n < orig_sz; n *= 2, lgn++);
        int s = 1 << (lgn - 1)/3;  // the number of columns is a power of 2
        int r = n / s;             // the number of rows is also a power of 2
        fs.growTo(n, _0_);
        for (int begin = 0, end = r; end <= n; begin = end, end += r)
            rangeOddEvenSort(fs, begin, end, ineq);         // Step 1: sort the values in columns
        transpose(fs, s);                                   // Step 2: place columns in row major order
        for (int begin = 0, end = r; end <= n; begin = end, end += r)
            rangeOddEvenSort(fs, begin, end, ineq);         // Step 3: sort the values in columns
        untranspose(fs, s);                                 // Step 4: place rows in column major order 
        for (int begin = 0, end = r; end <= n; begin = end, end += r)
            rangeOddEvenSort(fs, begin, end, ineq);         // Step 5: sort the values in columns
        for (int begin = 0, end = r/2; end <= n + r/2; begin = end, end += r)
            rangeOddEvenSort(fs, begin, min(end, n), ineq); // Step 6,7,8: shift and sort the values in columns
        fs.shrink(n - orig_sz);
    }
}
