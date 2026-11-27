"""A fixed fully bonded 3-regular two-dimensional Ising crystal. Lookup by geometric cell and edge."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import argparse
import json
from functools import lru_cache
from fractions import Fraction as F
from square_ising import CircuitSlab
from slab_lookup import exchange
from cubic_slab import exp_negative_bounds,slab_at_y


# Directions 0 east, 1 west, 2 north, 3 south, 4 rung.
BINS=(((1,),(0,3),(2,4)),((2,),(3,),(4,)))


class Crystal:
    def __init__(self,source=None):
        self.source=CircuitSlab() if source is None else source
        self.ids={(0,"site"):0,(1,"site"):4}
        self.scaffold=[]
        self.output=[]
        def port(t,d):
            return 4*t+1+next(i for i,ds in enumerate(BINS[t]) if d in ds)
        for t in (0,1):
            for k in range(3):
                self.scaffold.append(((0,0,4*t),(0,0,4*t+1+k),(t,"stub",k)))
        for t,d,dx,dy,back in ((0,0,1,0,1),(0,2,0,1,3),(1,2,0,1,3)):
            self.scaffold.append(((0,0,port(t,d)),(dx,dy,port(t,back)),(t,"cross",d)))
        self.scaffold.append(((0,0,port(0,4)),(0,0,port(1,4)),(0,"cross",4)))
        self.scaffold.extend([((0,0,1),(0,0,5),(0,"neutral",0)),
                              ((0,0,6),(0,0,7),(0,"neutral",1))])
        self.size=8
        for sid,(a,b,rule) in enumerate(self.scaffold):
            if rule[1]=="stub":
                self.output.append((a,b,None))
                continue
            h,k,p,q=((0,0,self.size+i) for i in range(4))
            self.size+=4
            self.output.extend([(a,h,(sid,"stem") if rule==(0,"cross",4) else None),
                                (k,b,None),(h,p,None),(h,q,None),(p,k,None),(q,k,(sid,"off")),(p,q,None)])

    @lru_cache(maxsize=128)
    def around(self,x,y,t):
        p=(x,y,t)
        nbr=((x+1,y,t),(x-1,y,t),(x,y+1,t),(x,y-1,t),(x,y,1-t))
        ret=tuple((d,j) for d,q in enumerate(nbr) if (j:=exchange(self.source,p,q)))
        assert all(sum(d in ds for d,_ in ret)<=1 for ds in BINS[t])
        assert all(any(d in ds for ds in BINS[t]) for d,_ in ret)
        return ret

    def selected(self,x,y,rule):
        t,kind,i=rule
        if kind=="neutral":
            return 0
        act=self.around(x,y,t)
        if kind=="cross":
            return dict(act).get(i,0)
        return int(any(d in BINS[t][i] for d,_ in act))

    def edge(self,x,y,i):
        if not 0<=i<len(self.output):
            raise ValueError("geometric edge id out of range")
        a,b,sw=self.output[i]
        sig=1
        if sw is not None:
            sid,kind=sw
            J=self.selected(x,y,self.scaffold[sid][2])
            sig=-1 if (kind=="off" and J==0 or kind=="stem" and J<0) else 1
        return (a[0]+x,a[1]+y,a[2]),(b[0]+x,b[1]+y,b[2]),sig


def crystal_bounds(s,b):
    bits=s.length.bit_length()+180
    lo,hi=exp_negative_bounds(2*b,bits)
    def reduced(y):
        t=(1-y)/(1+y)
        tau=2*t**4*(1+t)/(1+2*t**3+t**4)
        rho=t*t*tau
        return (1-rho)/(1+rho)
    return slab_at_y(s,reduced(lo),reduced(hi),bits)


def window(s):
    result=[]
    for left,right in ((F(3,4),F(19,25)),(F(13,20),F(2,3))):
        lo,hi=F(0),F(64)
        for _ in range(90):
            x=(lo+hi)/2
            a,b=crystal_bounds(s,x)
            if left<a<=b<right:
                result.append(x)
                break
            if a+b>left+right:
                lo=x
            else:
                hi=x
        else:
            raise ArithmeticError("crystal temperature bracket failed")
    return result


def runcheck(c):
    from collections import Counter
    from itertools import combinations
    deg=Counter(a[2] for e in c.output for a in e[:2])
    assert len(deg)==c.size and set(deg.values())=={3}
    assert len({frozenset((a,b)) for a,b,_ in c.output})==len(c.output)
    mid=[a[2] for e in c.output if e[2] is not None for a in e[:2]]
    assert len(set(mid))==len(mid)
    from itertools import product
    # Check the four-spin diamond with the actual unit sign choices.
    for t in (F(1,4),F(2,3)):
        tau=2*t**4*(1+t)/(1+2*t**3+t**4)
        for J in (-1,0,1):
            totals=[]
            for end in (-1,1):
                z=F(0)
                for h,k,p,q in product((-1,1),repeat=4):
                    z+=(1+(-1 if J<0 else 1)*t*h)*(1+t*k*end)*(1+t*h*p)*(1+t*h*q)*(1+t*p*k)*(1+(-1 if J==0 else 1)*t*q*k)*(1+t*p*q)
                totals.append(z)
            assert (totals[1]-totals[0])/(totals[1]+totals[0])==J*tau
    # Enumerate the possible direction sets at interior segment endpoints.
    allowed0=((0,1,2),(0,1),(1,2),(1,3),(0,4),(1,4),(3,4))
    allowed1=((2,3),(2,4),(3,4))
    for layer,allowed in enumerate((allowed0,allowed1)):
        for ds in allowed:
            assert all(sum(d in group for d in ds)<=1 for group in BINS[layer])
    # Visit actual full-size route bends as well as abstract port cases.
    s=c.source
    for mod in (0,1,2,3,3*s.graph.W,4*s.graph.W):
        for i in (0,s.graph.estarts[mod+1]-s.graph.estarts[mod]-1):
            pts,expected=s.path((mod,i),(-1,2))
            for point in pts:
                c.around(*point)
            for j,(a,b) in enumerate(zip(pts,pts[1:])):
                axis=next(k for k in range(3) if a[k]!=b[k])
                step=1 if b[axis]>a[axis] else -1
                d=((0,1),(2,3),(4,4))[axis][int(step<0)]
                assert dict(c.around(*a))[d]==(expected if j==s.signed_segment else 1)
    for x,lo,hi in zip(window(c.source),(F(3,4),F(13,20)),(F(19,25),F(2,3))):
        a,b=crystal_bounds(c.source,x)
        assert lo<a<=b<hi


def main():
    p=argparse.ArgumentParser(description=__doc__)
    subs=p.add_subparsers(dest="cmd",required=True)
    subs.add_parser("describe")
    subs.add_parser("check")
    e=subs.add_parser("edge")
    for k in ("x","y","edge_index"):
        e.add_argument(k,type=int)
    args=p.parse_args()
    c=Crystal()
    if args.cmd=="edge":
        res=c.edge(args.x,args.y,args.edge_index)
    else:
        if args.cmd=="check":
            runcheck(c)
        s=c.source
        res={"spins_per_geometric_cell":c.size,"bonds_per_geometric_cell":len(c.output),
             "signed_cell_spins":c.size*16*s.px*s.py,"window":[str(x) for x in window(s)],
             "degree":3,"observed_site":[s.vertex_start+4,0,c.ids[0,"site"]],"lag":[0,4*s.py,0]}
    print(json.dumps(res,indent=2))


if __name__=="__main__":
    main()

