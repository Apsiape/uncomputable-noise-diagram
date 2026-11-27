"""Unit signed exchanges for the fanout-two trivalent Boolean circuit magnet."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from fractions import Fraction as F
from functools import lru_cache
import argparse
import json
from bond_circuit import ZERO,ONE,COPY,NOT,AND,OR
from cubic_ising import core_edge,tree_edge,tree_node,tables,evaluate
from circuit_ising import power_bounds
from herald_circuit import gate,gate_count


from array import array
from bisect import bisect_right
from herald_circuit import users,network
from herald_blocks import block


@lru_cache(maxsize=16)
def gate_word(f):
    return sum((((f >> (2*((j >> 3)&1)+((j >> 2)&1)))&1)^((j >> 1)&1)^(j&1)) << j for j in range(16))


PAIR=sum(((i >> 3)&1) << i for i in range(16))
FOUR=sum((((i >> 3)^(i >> 2))&1) << i for i in range(16))


def profile(f):
    return 4 if f in (AND,OR) else 1 if f in (ZERO,ONE) else 2 if f in (COPY,NOT) else 3


class HeraldGraph:
    p=105
    def __init__(self,W=None):
        self.W=gate_count() if W is None else W
        self.mods=5*self.W+2
        self.loop=2*self.p+14
        self.rail=self.loop+self.W+1
        self.herald=self.rail+2*self.W
        self.chain=self.herald+2*self.W
        self.base=self.chain+2*self.W+2
        self.vstarts=array("Q",[self.base])
        self.estarts=array("Q",[0])
        for i in range(self.mods):
            part=block(self.word(i))
            self.vstarts.append(self.vstarts[-1]+part.private)
            self.estarts.append(self.estarts[-1]+len(part.edges))
        self.V=self.vstarts[-1]
        self.E=self.estarts[-1]

    def word(self,i):
        if i<3*self.W:
            g,k=divmod(i,3)
            return (gate_word(self.gate(g)[0]) if k==0 else PAIR+(profile(self.gate(g)[0]) << 16) if k==1 else FOUR)
        if i==3*self.W:
            return FOUR
        j=i-3*self.W-1
        if j%2==0 and j//2<self.W:
            return PAIR+(profile(self.gate(j//2)[0]) << 16)
        return PAIR

    def users(self,src):
        return users(src)

    def pair(self,source):
        if source>=0:
            return tuple(((0,0),self.rail+2*source+j) for j in (0,1))
        i=-1-source
        role,k=divmod(i,self.p)
        if role<3:
            cell=((0,0),(1,0),(0,1))[role]
            if k==0:
                return (cell,0),((0,0),2*self.p-1)
            return (cell,2*k-1),(cell,2*k)
        j=i-3*self.p
        if j<7:
            return tuple(((0,0),2*self.p+2*j+r) for r in (0,1))
        return ((0,0),self.chain),((0,0),self.chain+2*self.W+1)

    def gate(self,i):
        return gate(i)

    @lru_cache(maxsize=96)
    def module(self,i):
        if not 0<=i<self.mods:
            raise ValueError("module index outside cell")
        port=[None]*8
        def put(k,pair):
            port[2*k:2*k+2]=pair
        def raw(*ids):
            return tuple(((0,0),j) for j in ids)
        if i<3*self.W:
            g,k=divmod(i,3)
            h=raw(self.herald+2*g,self.herald+2*g+1)
            if k==0:
                f,a,b=self.gate(g)
                if f not in (ZERO,ONE):
                    put(0,self.pair(a))
                if f not in (ZERO,ONE,COPY,NOT):
                    put(1,self.pair(b))
                put(2,self.pair(g))
                put(3,h)
            elif k==1:
                put(0,h)
            else:
                put(0,h)
                put(1,raw(self.loop+g,self.loop+g+1))
        elif i==3*self.W:
            put(0,raw(self.loop,self.loop+self.W))
            put(1,self.pair(self.W-1))
        else:
            j=i-3*self.W-1
            put(0,raw(self.chain+j,self.chain+j+1))
        return tuple(port),self.word(i)

    def edge(self,module,local):
        ports,word=self.module(module)
        part=block(word)
        if not 0<=local<len(part.edges):
            raise ValueError("edge index outside module")
        a,b,s=part.edges[local]
        def external(x):
            return ports[-1-x] if x<0 else ((0,0),self.vstarts[module]+x)
        return external(a),external(b),s

    def port(self,v,other,address,first):
        cell,x=v
        mod,k=address
        if x>=self.base:
            return block(self.word(mod)).incidences[x-self.vstarts[mod]].index(k)
        if x<2*self.p:
            return ((self.gate(mod//3)[1]*-1-1)//self.p)
        if x<self.loop:
            return 0
        if x<self.rail:
            j=x-self.loop
            return 0 if mod==3*self.W else 1+int(mod//3==j)
        if x<self.herald:
            producer=(x-self.rail)//2
            if mod==3*producer:
                return 0
            if mod==3*self.W:
                return 1
            return 1+self.users(producer).index(mod//3)
        if x<self.chain:
            return mod%3
        j=x-self.chain
        return 0 if mod<3*self.W else 1+int(mod-3*self.W-1==j)

    def describe(self):
        return {"gate_count":self.W,"truth_modules":self.mods,"spins_per_cell":self.V,
                "edges":self.E,"maximum_degree":3,"window":[str(x) for x in window(self.W)]}


@lru_cache(maxsize=1)
def exponents(W):
    ops,_=network()
    assert W==len(ops)
    tags=[profile(f) for f,_,_ in ops]
    nonlinear=tags.count(4)
    return 1+W+sum(min(k,3) for k in tags),nonlinear,5*nonlinear


def z_at_y(y,W):
    if y==0:
        return F(5,8),F(5,8)
    plus,minus=tables()
    p,n=evaluate(plus,y),evaluate(minus,y)
    c=(n*n-p*p)/(n*n+p*p)
    s=(1-y)/(1+y)
    u=(n-p)/(n+p)
    lo=hi=F(1)
    for val,deg in zip((u,c,s),exponents(W)):
        a,b=power_bounds(val,deg,125)
        lo*=a
        hi*=b
    return 1-3*hi/8,1-3*lo/8


def window(W):
    from cubic_slab import exp_negative_bounds
    result=[]
    for left,right in ((F(3,4),F(19,25)),(F(13,20),F(2,3))):
        lo,hi=F(0),F(40)
        for _ in range(80):
            mid=(lo+hi)/2
            yl,yh=exp_negative_bounds(2*mid,160)
            a,b=z_at_y(yl,W)[0],z_at_y(yh,W)[1]
            if left<a<=b<right:
                result.append(mid)
                break
            if a+b>left+right:
                lo=mid
            else:
                hi=mid
        else:
            raise ArithmeticError("herald window bracket failed")
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__)
    s=p.add_subparsers(dest="command",required=True)
    s.add_parser("describe")
    e=s.add_parser("edge")
    e.add_argument("module",type=int)
    e.add_argument("local",type=int)
    args=p.parse_args()
    g=HeraldGraph()
    result=g.describe() if args.command=="describe" else g.edge(args.module,args.local)
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()

