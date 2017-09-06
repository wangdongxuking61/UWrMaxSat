#ifndef HashQueue_h
#define HashQueue_h

#include <climits>
#include "Global.h"
#include "minisat/mtl/Vec.h"
#include "Map.h"
#include "Heap.h"

static const int prime[] = { 2, 3, 5, 7, 11, 13, 17 };
static const int primeIndex[] = {0, 0, 1, 2, 0, 3, 0, 4, 0, 0, 0, 5, 0, 6, 0, 0, 0, 7};

constexpr size_t log2(size_t n) { return ( (n<2) ? 1 : 1+log2(n/2)); }
constexpr size_t pbits = log2(elemsof(prime)), pmask = (1 << pbits) - 1;

//static bool cmp(int left, int right);

class HashQueue {
    struct BaseData {
        long long int base;
        int cost;
        int carry_ins;
        int index;
    } ;
    struct Comp {
        vec<BaseData * > *mapptr;
        bool operator()(int i, int j) { return (*mapptr)[i]->cost < (*mapptr)[j]->cost ; }
        Comp(vec<BaseData * > *ptr) : mapptr(ptr) { }
    } ;
    Map<int, BaseData> baseMap;
    vec<BaseData * > mapPtr;
    int lastFree;
    Comp mycmp;
    Heap<Comp> queue;
    static const BaseData nullBase;
    void unpackBase(long long int base, vec<int>& nbase) {
        nbase.clear(); while (base & pmask) { nbase.push(prime[(base & pmask) - 1]); base >>= pbits; }
    }
    long long int packBase(const vec<int>& nbase) {
        long long int base = 0;
        for (int i=0; i < nbase.size(); i++) 
            base = (base << pbits) | primeIndex[nbase[i]];
        return base;
    }
    int hashBase(const vec<int>& nbase) {
        int count[elemsof(prime)] = {0}, hash = 0;
        for (int i=0; i < nbase.size(); i++) 
            count[primeIndex[nbase[i]]-1]++;
        for (int i = (int)elemsof(prime) - 1; i >= 0; i--) 
            hash = ((hash << 1) | 1) << count[i];
        return hash;
    }
public:
    HashQueue(int capacity = 1) : baseMap(nullBase, capacity), lastFree(-1), mycmp(&mapPtr), queue(mycmp) { }
    void clear(void) { mapPtr.clear(); }
    static const int maxBaseSize;
    bool isEmpty() { return queue.empty(); }
    int popMin(vec<int> &new_base, int &carry_ins) {
        if (queue.empty()) return INT_MAX;
        int minIndex = queue.getmin();
        BaseData *minPtr = mapPtr[minIndex];
        queue.indices[minIndex] = lastFree;
        lastFree = minIndex;
        minPtr->index = -1;
        unpackBase(minPtr->base, new_base);
        carry_ins = minPtr->carry_ins;
        return minPtr->cost;
    }
    void push(const vec<int>& base, int cost, int carry_ins) {
        int hash = hashBase(base);
        long long int pbase = packBase(base);
        BaseData &data = baseMap.ref(hash);
        if (cost < data.cost) {
            data.base = pbase;
            data.cost = cost;
            data.carry_ins = carry_ins;
            if (data.index == -1) {
                int new_index;
                if (lastFree != -1) 
                    new_index=lastFree,lastFree=queue.indices[lastFree],mapPtr[new_index] = &data;
                else 
                    new_index=queue.indices.size(), queue.indices.push(0), mapPtr.push(&data);
                queue.insert(new_index);
                data.index = new_index;
            } else 
                queue.increase(data.index);
        }
    }
};

const int HashQueue::maxBaseSize = sizeof(long long int)*CHAR_BIT / pbits;

const HashQueue::BaseData HashQueue::nullBase = {0, INT_MAX, 0, -1};
/*vec<HashQueue::BaseData *> HashQueue::mapPtr;

static bool cmp(int left, int right) {
        return HashQueue::mapPtr[left]->cost < HashQueue::mapPtr[right]->cost ; 
}*/

#endif