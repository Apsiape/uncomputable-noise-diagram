"""Exact terminal-weight polynomials of a degree-four, one-contact parity gadget."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from itertools import product
from functools import lru_cache
from math import comb
from fractions import Fraction as F

PAIRINGS=(((0,1),(2,3)),((0,2),(1,3)),((0,3),(1,2)))


def signed(port,center):
    return 1-2*((port & center).bit_count()%2)


def convolution(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j]+=x*y
    return out


@lru_cache(maxsize=500)
def branch(external,core,port,pairing):
    vals=[0]*8
    for hub,u,v in product((-1,1),repeat=3):
        cost=int(hub!=external)
        for child,group in zip((u,v),PAIRINGS[pairing]):
            cost+=int(child!=hub)
            cost+=sum(child*signed(port,c)*core[c]<0 for c in group)
        vals[cost]+=1
    return vals


def polynomial(terminals,pairings):
    co=[0]*29
    for core in product((-1,1),repeat=4):
        vec=[1]
        for i,s in enumerate(terminals):
            vec=convolution(vec,branch(s,core,i,pairings[i]))
        co=[a+b for a,b in zip(co,vec)]
    return co


def degrees(p):
    return next(i for i,c in enumerate(p) if c)


def monotonicity_certificate():
    pairings=(0,0,0,0)
    plus=polynomial((1,1,1,1),pairings)
    minus=polynomial((-1,1,1,1),pairings)
    for s in product((-1,1),repeat=4):
        assert polynomial(s,pairings)==(plus if s.count(-1)%2==0 else minus)
    # t=e^(2b)-1. Transform y=1/(1+t) and clear the common denominator.
    def shifted(p):
        return [sum(c*comb(28-j,i) for j,c in enumerate(p) if i<=28-j) for i in range(29)]
    P,N=shifted(plus),shifted(minus)
    derivative=lambda p:[i*c for i,c in enumerate(p) if i]
    first=convolution(derivative(N),P)
    second=convolution(N,derivative(P))
    cert=[a-b for a,b in zip(first,second)]
    assert min(cert)>=0 and max(cert)>0
    return degrees(plus),degrees(minus),min(i for i,c in enumerate(cert) if c),max(i for i,c in enumerate(cert) if c)


def main():
    choices=[]
    for pairings in product(range(3),repeat=4):
        pos=polynomial((1,1,1,1),pairings)
        neg=polynomial((-1,1,1,1),pairings)
        if degrees(pos)!=degrees(neg):
            choices.append((pairings,degrees(pos),degrees(neg)))
    print("ground-separated choices",len(choices),"sample",choices[:8],flush=True)
    if choices:
        pairing=choices[0][0]
        print("positive",polynomial((1,1,1,1),pairing))
        print("negative",polynomial((-1,1,1,1),pairing))
        print("monotonicity and full terminal checks",monotonicity_certificate())


if __name__=="__main__":
    main()

