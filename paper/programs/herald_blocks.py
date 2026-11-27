"""One-contact degree-three parity and conditional Boolean sign factors of identical strength."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from functools import lru_cache
from cubic_ising import core_edge


class Block:
    def __init__(self):
        self.private=0
        self.edges=[]
        self.incidences={}
        self.slot_edges={}

    def new(self):
        n=self.private
        self.private+=1
        return n

    def add(self,a,b,sign=1):
        assert a!=b
        k=len(self.edges)
        self.edges.append((a,b,sign))
        for v in (a,b):
            self.incidences.setdefault(v,[]).append(k)
            if v<0:
                self.slot_edges[-v-1]=k

    def path(self,a,b,n,sign=1):
        for _ in range(n-1):
            c=self.new()
            self.add(a,c,sign)
            a,sign=c,1
        self.add(a,b,sign)

    def core(self,slots,sgn=1):
        idx={}
        for i in range(32):
            a,b,s=core_edge(("core",),slots,sgn,i)
            def vertex(v):
                if isinstance(v,int):
                    return v
                if v not in idx:
                    idx[v]=self.new()
                return idx[v]
            self.add(vertex(a),vertex(b),s)

    def pair_series(self,a,b,n):
        for j in range(n):
            v=b if j==n-1 else self.new()
            pad=self.new()
            self.core((a,v,pad,pad))
            a=v

    def calibrated(self,tag):
        if tag<4:
            self.pair_series(-1,-2,tag)
            return
        x,y,z=(self.new() for _ in range(3))
        self.path(-1,x,2)
        for _ in range(2):
            pad=self.new()
            self.core((x,y,pad,pad))
        self.path(y,z,3)
        self.pair_series(z,-2,3)

    def parity(self,slots,sgn):
        leaves=[-1-s for s in slots]
        if len(leaves)==2:
            pad=self.new()
            leaves.extend((pad,pad))
        n=len(leaves)//2-1
        for i in range(n):
            if i+1==n:
                group=leaves
            else:
                nxt=self.new()
                group=[*leaves[:3],nxt]
                leaves=[nxt,*leaves[3:]]
            self.core(group,sgn if i==0 else 1)

    def conditional(self,is_or):
        # a,b,y,h are decision signs, each represented by one external pair.
        master=self.new()
        data=[self.new(),self.new()]
        for side in range(2):
            if side==int(not is_or):
                terms=(-3,-4)
                sign=1
            else:
                pad=self.new()
                terms=(pad,pad)
                sign=-1 if is_or else 1
            self.core((master,data[side],*terms),sign)
        u=(self.new(),self.new())
        self.add(-1,u[0])
        self.add(-2,u[1])
        v=(self.new(),self.new())
        self.path(*v,2)
        arms=[self.new(),self.new()]
        for side in range(2):
            self.core((arms[side],data[side],*v))
            self.core((arms[side],data[side],*u),-1 if side else 1)
        join,out=self.new(),self.new()
        self.add(arms[0],join)
        self.add(arms[1],join)
        self.add(join,out)
        for i in (4,6):
            nxt=self.new()
            self.core((out,nxt,-1-i,-2-i))
            out=nxt
        self.add(out,master)

    def verify(self):
        assert max(map(len,self.incidences.values()))<=3
        assert all(len(v)==1 for k,v in self.incidences.items() if k<0)
        assert len({tuple(sorted((a,b))) for a,b,_ in self.edges})==len(self.edges)


@lru_cache(maxsize=32)
def block(key):
    tag,word=divmod(key,1 << 16)
    b=Block()
    if tag:
        b.calibrated(tag)
        b.verify()
        return b
    constant=word&1
    chosen=[i for i in range(4) if constant!=((word >> (1 << (3-i)))&1)]
    recon=sum((constant^(sum((j >> (3-i))&1 for i in chosen)%2)) << j for j in range(16))
    if recon==word:
        b.parity([2*i+r for i in chosen for r in (0,1)],(-1)**constant)
    else:
        for is_or in (False,True):
            def val(j):
                a,x,y,h=((j >> k)&1 for k in (3,2,1,0))
                return (a|x if is_or else a&x)^y^h
            if sum(val(j) << j for j in range(16))==word:
                b.conditional(is_or)
                break
        else:
            raise ValueError("unrecognized non-affine Boolean predicate")
    b.verify()
    return b

