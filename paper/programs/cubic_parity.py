"""Check a trivalent parity block by tracing its sixteen terminal conditions."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from itertools import product
from math import comb
from functools import lru_cache
from parity_core import PAIRINGS,branch,convolution,degrees


@lru_cache(maxsize=8)
def weights(terminals,hub_pairing=0,center_pairing=0):
    co=[0]*33
    first=PAIRINGS[center_pairing][0]
    for low in product((-1,1),repeat=4):
        for high in product((-1,1),repeat=4):
            cost=sum(a!=b for a,b in zip(low,high))
            vec=[1]
            for i,s in enumerate(terminals):
                vec=convolution(vec,branch(s,low if i in first else high,i,hub_pairing))
            for j,v in enumerate(vec):
                co[j+cost]+=v
    return tuple(co)


def certificate(plus,minus):
    deg=len(plus)-1
    def shift(p):
        return [sum(c*comb(deg-j,i) for j,c in enumerate(p) if i<=deg-j) for i in range(deg+1)]
    P,N=shift(plus),shift(minus)
    derivative=lambda p:[i*c for i,c in enumerate(p) if i]
    first=convolution(derivative(N),P)
    second=convolution(N,derivative(P))
    return tuple(a-b for a,b in zip(first,second))


def main():
    for h in range(3):
        for c in range(3):
            plus=weights((1,1,1,1),h,c)
            minus=weights((-1,1,1,1),h,c)
            cert=certificate(plus,minus)
            print("hub",h,"center",c,"ground costs",degrees(plus),degrees(minus),
                  "nonnegative derivative",min(cert)>=0,"strict",max(cert)>0,flush=True)


if __name__=="__main__":
    main()

