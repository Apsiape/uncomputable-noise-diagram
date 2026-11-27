"""Equal-length, vertex-disjoint cubic-lattice wires for every edge of the trivalent magnet."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from fractions import Fraction as F
import argparse
import json
from cubic_ising import CubicGraph,z_at_y
from circuit_ising import power_bounds


def subcore(parts):
    kind,i,*a=parts
    if kind=="hub":
        return i
    if kind=="child":
        return 4+2*i+a[0]
    if kind=="center":
        return 12+2*i+a[0]
    raise ValueError("unknown core spin")


def tree_rank(stem,kind,i):
    return i-1 if kind=="stem" else stem+i-2


class Slab:
    def __init__(self,graph=None):
        self.graph=graph if graph is not None else CubicGraph()
        g=self.graph
        self.N=1 << g.m
        self.vcal=g.ordinary+44*g.m+35
        self.ecal=g.ordinary+65*g.m+49
        trees=0
        self.control_starts=[]
        for i in range(g.m):
            self.control_starts.append(trees)
            trees+=2*(g.m-i+(1 << (i+1))-2)
        master=(1 << (g.m+8))-1
        def offsets(names,sizes):
            total=0
            result={}
            for name,size in zip(names,sizes,strict=True):
                result[name]=total
                total+=size
            return result,total
        self.vo,self.V=offsets(("site","control","broadcast","mux","average","cal"),
                         (2*g.p+1,trees,master,(self.N-1)*(2*g.m+85),381*self.N,18*self.N*self.vcal))
        self.eo,self.E=offsets(("close","control","master","mux","average","cal"),
                         (1,trees,master,(self.N-1)*(2*g.m+131),635*self.N,18*self.N*self.ecal))
        self.set_geometry()

    def parent_z(self,y):
        return z_at_y(y,self.graph.m)

    def set_geometry(self):
        self.colors=16*self.E
        self.vertex_start=8*((self.colors+7)//8)+32
        self.py=8*(self.colors+4)
        self.px=4*(self.vertex_start+8*(self.V+1)+self.py+32)
        self.length=4*self.px+100
        assert not self.length%2

    def ctl(self,i,rail):
        return self.control_starts[i]+rail*(self.graph.m-i+(1 << (i+1))-2)

    def vrank(self,v):
        _,kind,*a=v
        g=self.graph
        if kind=="spin":
            return 0
        if kind=="invariant":
            i,rail=a
            return 1+2*i+rail
        if kind in ("reference","master"):
            return 2*g.p-1+(kind=="master")
        off=self.vo[kind]
        if kind=="control":
            i,rail,loc,k=a
            return off+self.ctl(i,rail)+tree_rank(g.m-i,loc,k)
        if kind=="broadcast":
            return off+tree_rank(1,*a)
        if kind=="mux":
            n,loc,*p=a
            off+=(n-1)*(2*g.m+85)
            if loc=="arm":
                return off+p[0]
            if loc in ("join","out"):
                return off+2+(loc=="out")
            if loc=="constant":
                return off+4+p[0]
            return off+2*g.m+5+20*p[0]+subcore(p[1:])
        if kind=="average":
            leaf,n,loc=a
            return off+381*leaf+3*(n-1)+("sum","dummy","out").index(loc)
        leaf,slot,loc,j,*p=a
        off+=(18*leaf+slot)*self.vcal
        if loc=="plain":
            return off+j-1
        off+=g.ordinary
        if loc=="pair":
            off+=44*j
            if p[0] in ("join","out"):
                return off+(p[0]=="out")
            if p[0]=="pad":
                return off+2+p[1]
            return off+4+20*p[1]+subcore(p[2:])
        off+=44*g.m+5*j
        if p[0]=="input":
            return off+p[1]
        return off+2+("sum","dummy","out").index(p[0])

    def erank(self,address):
        kind,*a=address
        off=self.eo[kind]
        if kind=="close":
            return off
        if kind=="control":
            i,r,k=a
            return off+self.ctl(i,r)+k
        if kind=="master":
            return off+a[0]
        if kind=="mux":
            return off+(a[0]-1)*(2*self.graph.m+131)+a[1]
        if kind=="average":
            leaf,n,k=a
            return off+635*leaf+5*(n-1)+k
        leaf,slot,loc,j,*end=a
        off+=(18*leaf+slot)*self.ecal
        if loc=="plain":
            return off+j
        off+=self.graph.ordinary
        return off+65*j+end[0] if loc=="parity" else off+65*self.graph.m+7*j+end[0]

    def port(self,v,other,address,first):
        _,family,*a=v
        kind,*p=address
        edge=p[-1] if p else 0
        if family in ("spin","invariant","reference"):
            return p[0]//self.graph.p
        if family=="master":
            return int(kind=="master")
        if "core" in a or "parity" in a:
            idx=a.index("core") if "core" in a else a.index("parity")
            role,i,*extra=a[idx+2:]
            sub=(edge%32)
            if role=="hub":
                return 0 if sub<4 else 1+(sub-4)%2
            if role=="child":
                return 0 if sub<12 else 1+(sub-12)%2
            return 0 if sub>=28 else 1+((sub-12)//4)%2
        if family in ("control","broadcast"):
            if kind in ("control","master"):
                if not first:
                    return 0
                return 1+(other[-1]%2 if other[-2]=="tree" else 0)
            if kind=="mux":
                return 1+edge//64
            return 1+(edge%2 if kind=="average" else 0)
        if family=="mux":
            n,loc,*rest=a
            if loc=="arm":
                return 2 if edge>=128 else (edge//32)%2
            if loc=="join":
                return 2 if edge==130 else edge-128
            if loc=="constant":
                if edge<128:
                    return 1+edge//64
                return 0 if rest[0] in (0,2*self.graph.m) else int(first)
            if kind=="close":
                return 1
            return 0 if p[0]==n else 1+(edge//32)%2
        if family=="average":
            leaf,n,loc=a
            if loc in ("sum","dummy"):
                return 2 if edge==4 else edge//2
            if kind=="mux":
                return 1+(edge//32)%2
            return 0 if p[1]==n else 1+edge%2
        leaf,slot,loc,j,*rest=a
        if loc=="plain":
            if p[2]=="plain":
                return int(first)
            return 1+edge//32
        if loc=="pair":
            typ=rest[0]
            if typ=="pad":
                return edge%32-2
            if typ=="join":
                return 2 if edge==64 else edge//32
            if p[2]=="average":
                return 1+edge
            return 0 if p[3]==j else 1+edge//32
        typ=rest[0]
        if typ=="input":
            return 0 if edge<2 else 1+(edge-2)%2
        if typ in ("sum","dummy"):
            return 2 if edge==6 else (edge-2)//2
        if kind=="average":
            return 1+edge%2
        return 0 if p[3]==j else 1+edge

    def path(self,address,cell=(0,0)):
        a,b,sign=self.graph.edge(*address)
        ends=[]
        for x,y,first in ((a,b,True),(b,a,False)):
            (dx,dy),*_=x
            origin=((cell[0]+dx)*self.px+self.vertex_start+8*self.vrank(x)+4,(cell[1]+dy)*self.py,0)
            p=self.port(x,y,address,first)
            if p not in (0,1,2):
                raise ValueError(("invalid port",x,address,p))
            sx,sy=((-1,0),(1,0),(0,1))[p]
            ends.append((origin,(origin[0]+sx,origin[1]+sy,0)))
        # Put the lower row first. Its local stub ends before the upper horizontal run.
        (u,up),(v,vp)=sorted(ends,key=lambda item:item[0][1])
        j=16*self.erank(address)+cell[0]%4+4*(cell[1]%4)
        x1,y1,_=up
        x2,y2,_=vp
        assert x1!=x2
        trunk=(min(x1,x2)//self.px)*self.px+j
        la,lb=u[1]+8*j+8,v[1]+8*j+12
        base=8+(la-y1)+(lb-y2)+(lb-la)+(x1-trunk)+(x2-trunk)
        difference=self.length-base
        assert difference>0 and difference%2==0
        turn=x1+difference//2
        assert max(turn,x2)-trunk<4*self.px
        assert la+1<lb and la<u[1]+self.py and lb<v[1]+self.py
        points=(u,up,(x1,y1,1),(x1,la,1),(x1,la,0),(turn,la,0),(turn,la+1,0),
                (trunk,la+1,0),(trunk,la+1,1),(trunk,lb,1),(trunk,lb,0),(x2,lb,0),
                (x2,lb,1),(x2,y2,1),vp,v)
        return points,sign

    def describe(self):
        return {"in_plane_periods":[4*self.px,4*self.py],"z_planes":[0,1],
                "path_length":self.length,"active_exchange_values":[-1,1],
                "unused_nearest_neighbor_bonds":0,"spectator_spins":"independent and unbiased",
                "window":[str(x) for x in window(self)]}


def exp_negative_bounds(x,bits):
    # Range reduction keeps the Taylor sum short even at the slab temperature.
    scale=1 << bits
    reductions=0
    while x>1:
        x/=2
        reductions+=1
    term=total=F(1)
    n=0
    while term*scale>F(1,256):
        n+=1
        term*=x/n
        total+=term
    upper=total+term*x/(n+1)/(1-x/(n+2))
    a,b=F(1,upper),F(1,total)
    lo=(a*scale).__floor__()
    hi=(b*scale).__ceil__()
    for _ in range(reductions):
        lo=lo*lo//scale
        hi=(hi*hi+scale-1)//scale
    return F(lo,scale),F(hi,scale)


def slab_z_bounds(slab,b):
    bits=slab.length.bit_length()+150
    lo,hi=exp_negative_bounds(2*b,bits)
    return slab_at_y(slab,lo,hi,bits)


def slab_at_y(slab,lo,hi,bits):
    ta=(1-hi)/(1+hi)
    tb=(1-lo)/(1+lo)
    l=power_bounds(ta,slab.length,bits)[0]
    h=power_bounds(tb,slab.length,bits)[1]
    # Convert effective tanh to exp(-2b') and round outwards before the finite polynomial evaluation.
    scale=1 << 120
    yl=F((((1-h)/(1+h))*scale).__floor__(),scale)
    yh=F((((1-l)/(1+l))*scale).__ceil__(),scale)
    return slab.parent_z(yl)[0],slab.parent_z(yh)[1]


def window(slab):
    result=[]
    for left,right in ((F(3,4),F(19,25)),(F(13,20),F(2,3))):
        lo,hi=F(0),F(slab.length.bit_length()+20)
        for _ in range(90):
            mid=(lo+hi)/2
            a,b=slab_z_bounds(slab,mid)
            if left<a<=b<right:
                result.append(mid)
                break
            if a+b>left+right:
                lo=mid
            else:
                hi=mid
        else:
            raise ArithmeticError("slab window bracket failed")
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    cmds=parser.add_subparsers(dest="command",required=True)
    cmds.add_parser("describe")
    pa=cmds.add_parser("path")
    pa.add_argument("address",help="JSON trivalent edge address")
    pa.add_argument("--cell",nargs=2,type=int,default=(0,0))
    args=parser.parse_args()
    slab=Slab()
    result=slab.describe() if args.command=="describe" else slab.path(json.loads(args.address),args.cell)
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()

