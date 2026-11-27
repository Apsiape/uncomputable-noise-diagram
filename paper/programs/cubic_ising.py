"""One-contact ferromagnetic/antiferromagnetic routers on a periodic graph of degree three."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from fractions import Fraction as F
from functools import lru_cache
import argparse
import json

from cubic_parity import weights
from parity_core import signed
from circuit_ising import power_bounds
from small_ising import Encoding


def core_edge(label,terminals,orientation,i):
    if not 0<=i<32:
        raise ValueError("four-port block edge must be in 0..31")
    hub=lambda p:(*label,"hub",p)
    child=lambda p,g:(*label,"child",p,g)
    center=lambda c,k:(*label,"center",c,k)
    if i<4:
        return terminals[i],hub(i),(-orientation if i==0 else 1)
    if i<12:
        p,g=divmod(i-4,2)
        return hub(p),child(p,g),1
    if i<28:
        p,c=divmod(i-12,4)
        return child(p,c//2),center(c,p//2),signed(p,c)
    return center(i-28,0),center(i-28,1),1


def tree_node(label,stem,n):
    return (*label,"stem",stem) if n==1 else (*label,"tree",n)


def tree_edge(label,source,stem,height,i):
    size=stem+(1 << (height+1))-2
    if not 0<=i<size or stem<1:
        raise ValueError("broadcast edge out of range")
    if i<stem:
        return source if i==0 else (*label,"stem",i),(*label,"stem",i+1),1
    n=i-stem+2
    return tree_node(label,stem,n//2),tree_node(label,stem,n),1


class CubicGraph:
    def __init__(self):
        self.parent=Encoding()
        self.p=self.parent.p
        self.m=3*self.p
        self.ordinary=2*self.m*self.m+2*self.m+2
        self.owner=(0,0)

    def local(self,*label):
        return (self.owner,*label)

    def control(self,level,rail):
        if not 0<=level<self.m or rail not in (0,1):
            raise ValueError("control address out of range")
        role,bit=divmod(level,self.p)
        cell=((0,0),(1,0),(0,1))[role]
        if bit==0:
            source=(cell,"spin") if rail==0 else self.local("reference")
        else:
            source=(cell,"invariant",self.p-1-bit,rail)
        return self.local("control",level,rail),source,self.m-level,level

    def master(self):
        return self.local("broadcast"),self.local("master"),1,self.m+7

    def decode(self,chunk):
        neg=chunk >> (self.p-1)
        data=chunk & ((1 << (self.p-1))-1)
        low=(1 << self.parent.pivot)-1
        rep=(data & low) | ((data & ~low) << 1)
        return rep ^ self.parent.flip if neg!=(self.parent.measured(rep)<0) else rep

    @lru_cache(maxsize=64)
    def energy(self,leaf):
        if not 0<=leaf<1 << self.m:
            raise ValueError("truth-table leaf outside range")
        mask=(1 << self.p)-1
        s,e,n=(self.decode((leaf >> (i*self.p)) & mask) for i in (2,1,0))
        return self.parent.model.horizontal(s,e)+self.parent.model.vertical(s,n)

    def slot(self,leaf,i):
        E=self.energy(leaf)
        source=tree_node(self.master()[0],1,(1 << (self.m+7))+128*leaf+i)
        if E==2 and i<18:
            return self.local("cal",leaf,i,"average",6,"out"),1
        plus=(64,40,7)[E]
        start=18 if E==2 else 0
        return source,1 if i<start+plus else -1

    def mux(self,n,i):
        if not 1<=n<1 << self.m or not 0<=i<2*self.m+131:
            raise ValueError("multiplexer address out of range")
        label=self.local("mux",n)
        level=n.bit_length()-1
        offset=n-(1 << level)
        h=lambda j:(*label,"arm",j)
        v=lambda j:(*label,"constant",j)
        if i<128:
            block,loc=divmod(i,32)
            arm,which=divmod(block,2)
            node=2*n+arm
            data=(self.local("mux",node,"out") if node<1 << self.m else
                  self.local("average",node-(1 << self.m),1,"out"))
            if which==0:
                controls=(v(0),v(2*self.m))
            else:
                controls=tuple(tree_node(self.control(level,j)[0],self.m-level,(1 << level)+offset)
                               for j in (0,1))
            orientation=-1 if arm==1 and which==1 else 1
            return core_edge((*label,"parity",block),(h(arm),data,*controls),orientation,loc)
        if i<130:
            return h(i-128),(*label,"join"),1
        if i==130:
            return (*label,"join"),(*label,"out"),1
        j=i-131
        return v(j),v(j+1),1

    def average(self,leaf,n,i):
        if not 0<=leaf<1 << self.m or not 1<=n<128 or not 0<=i<5:
            raise ValueError("averaging tree address out of range")
        label=self.local("average",leaf,n)
        if i==4:
            return (*label,"sum"),(*label,"out"),1
        side,dummy=divmod(i,2)
        child=2*n+side
        data,sign=((self.local("average",leaf,child,"out"),1) if child<128 else self.slot(leaf,child-128))
        return data,(*label,"dummy" if dummy else "sum"),(-sign if side and dummy else sign)

    def calibration(self,leaf,slot,kind,j,i=0):
        if not 0<=slot<18 or self.energy(leaf)!=2:
            raise ValueError("calibration is present only in slots 0..17 of energy-two leaves")
        label=self.local("cal",leaf,slot)
        initial=tree_node(self.master()[0],1,(1 << (self.m+7))+128*leaf+slot)
        if kind=="plain" and 0<=j<self.ordinary and i==0:
            return initial if j==0 else (*label,"plain",j),(*label,"plain",j+1),1
        if kind=="parity" and 0<=j<self.m and 0<=i<65:
            source=(*label,"plain",self.ordinary) if j==0 else (*label,"pair",j-1,"out")
            arm=(*label,"pair",j)
            if i==64:
                return (*arm,"join"),(*arm,"out"),1
            p,k=divmod(i,32)
            pad=(*arm,"pad",p)
            return core_edge((*arm,"core",p),(source,(*arm,"join"),pad,pad),1,k)
        if kind=="average" and 0<=j<7 and 0<=i<7:
            source=(*label,"pair",self.m-1,"out") if j==0 else (*label,"average",j-1,"out")
            arm=(*label,"average",j)
            if i<2:
                return source,(*arm,"input",i),1
            if i==6:
                return (*arm,"sum"),(*arm,"out"),1
            side,dummy=divmod(i-2,2)
            return (*arm,"input",side),(*arm,"dummy" if dummy else "sum"),(-1 if side and dummy else 1)
        raise ValueError("calibration edge out of range")

    def edge(self,kind,*indices):
        if kind=="control":
            level,rail,index=indices
            return tree_edge(*self.control(level,rail),index)
        if kind=="master":
            return tree_edge(*self.master(),*indices)
        if kind=="mux":
            return self.mux(*indices)
        if kind=="average":
            return self.average(*indices)
        if kind=="cal":
            return self.calibration(*indices)
        if kind=="close" and not indices:
            return self.local("master"),self.local("mux",1,"out"),1
        raise ValueError("unknown microscopic edge type")

    def describe(self):
        m=self.m
        leaves=1 << m
        twos=leaves*((1 << 14)-1)//(1 << 16)
        trees=2*sum(m-i+(1 << (i+1))-2 for i in range(m))
        master=(1 << (m+8))-1
        vertices=(2*self.p-1)+2+trees+master+(leaves-1)*(2*m+85)+leaves*127*3
        edges=trees+master+(leaves-1)*(2*m+131)+leaves*127*5+1
        vertices+=18*twos*(self.ordinary+44*m+35)
        edges+=18*twos*(self.ordinary+65*m+49)
        return {"maximum_degree":3,"visible_spins_per_cell":2*self.p-1,"decision_depth":m,
                "spins_per_cell":vertices,"edges_per_cell":edges,"energy_two_leaves":twos,
                "inverse_temperature_window":[str(x) for x in window(m)]}


def evaluate(p,x):
    value=F(0)
    for a in reversed(p):
        value=value*x+a
    return value


@lru_cache(maxsize=1)
def tables():
    return weights((1,1,1,1)),weights((-1,1,1,1))


def z_at_y(y,m):
    if y==0:
        return F(5,8),F(5,8)
    plus,minus=tables()
    P,N=evaluate(plus,y),evaluate(minus,y)
    c=(N*N-P*P)/(N*N+P*P)
    a=(1-y*y)/(1+y*y)
    t=(1-y)/(1+y)
    factors=[power_bounds(x,n,110) for x,n in ((t,2*m*m+3*m+16),(a,7),(c,m))]
    lo=hi=F(1)
    for l,h in factors:
        lo*=l
        hi*=h
    return 1-3*hi/8,1-3*lo/8


def effective_z_bounds(b,m):
    x=2*b
    assert 0<x<=40
    term=total=F(1)
    for i in range(1,201):
        term*=x/i
        total+=term
    upper=total+term*x/201/(1-x/202)
    scale=1 << 110
    ylo=F((scale/upper).__floor__(),scale)
    yhi=F((scale/total).__ceil__(),scale)
    return z_at_y(ylo,m)[0],z_at_y(yhi,m)[1]


def window(m):
    result=[]
    for left,right in ((F(3,4),F(19,25)),(F(13,20),F(2,3))):
        lo,hi=F(0),F(20)
        for _ in range(70):
            mid=(lo+hi)/2
            a,b=effective_z_bounds(mid,m)
            if left<a<=b<right:
                result.append(mid)
                break
            if a+b>left+right:
                lo=mid
            else:
                hi=mid
        else:
            raise ArithmeticError("degree-three temperature bracket not found")
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__)
    subs=p.add_subparsers(dest="command",required=True)
    subs.add_parser("describe")
    ed=subs.add_parser("edge")
    ed.add_argument("address",help='JSON list, for example ["mux",1,0]')
    leaf=subs.add_parser("leaf")
    leaf.add_argument("index",type=int)
    args=p.parse_args()
    graph=CubicGraph()
    if args.command=="describe":
        result=graph.describe()
    elif args.command=="leaf":
        result=graph.energy(args.index)
    else:
        result=graph.edge(*json.loads(args.address))
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()

