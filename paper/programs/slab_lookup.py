"""Coordinate lookup for the periodic two-layer magnet and its single-layer square realization."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from bisect import bisect_right
from cubic_incidence import candidates
from cubic_slab import Slab
import argparse
import json


def region(starts,i):
    keys=list(starts)
    key=keys[bisect_right([starts[k] for k in keys],i)-1]
    return key,i-starts[key]


def core_v(k):
    if k<4:
        return "hub",k
    if k<12:
        return "child",*divmod(k-4,2)
    return "center",*divmod(k-12,2)


def tree_v(stem,k):
    return ("stem",k+1) if k<stem else ("tree",k-stem+2)


def edge_unrank(s,i):
    if not 0<=i<s.E:
        return None
    key,k=region(s.eo,i)
    g=s.graph
    if key=="close":
        return ("close",)
    if key=="control":
        lev=bisect_right(s.control_starts,k)-1
        r,j=divmod(k-s.control_starts[lev],g.m-lev+(1 << (lev+1))-2)
        return key,lev,r,j
    if key=="master":
        return key,k
    if key=="mux":
        n,j=divmod(k,2*g.m+131)
        return key,n+1,j
    if key=="average":
        leaf,rest=divmod(k,635)
        n,j=divmod(rest,5)
        return key,leaf,n+1,j
    group,k=divmod(k,s.ecal)
    leaf,slot=divmod(group,18)
    if g.energy(leaf)!=2:
        return None
    prefix=(key,leaf,slot)
    if k<g.ordinary:
        return (*prefix,"plain",k)
    k-=g.ordinary
    return ((*prefix,"parity",*divmod(k,65)) if k<65*g.m else
            (*prefix,"average",*divmod(k-65*g.m,7)))


def vertex_unrank(s,i,cell):
    if not 0<=i<s.V:
        return None
    key,k=region(s.vo,i)
    g=s.graph
    if key=="site":
        if k==0:
            return cell,"spin"
        if k<2*g.p-1:
            return cell,"invariant",*divmod(k-1,2)
        return cell,("reference" if k==2*g.p-1 else "master")
    if key=="control":
        lev=bisect_right(s.control_starts,k)-1
        stem=g.m-lev
        r,j=divmod(k-s.control_starts[lev],stem+(1 << (lev+1))-2)
        return cell,key,lev,r,*tree_v(stem,j)
    if key=="broadcast":
        return cell,key,*tree_v(1,k)
    if key=="mux":
        n,k=divmod(k,2*g.m+85)
        prefix=(cell,key,n+1)
        if k<2:
            return *prefix,"arm",k
        if k<4:
            return *prefix,("join" if k==2 else "out")
        if k<2*g.m+5:
            return *prefix,"constant",k-4
        block,idx=divmod(k-2*g.m-5,20)
        return *prefix,"parity",block,*core_v(idx)
    if key=="average":
        leaf,r=divmod(k,381)
        n,j=divmod(r,3)
        return cell,key,leaf,n+1,("sum","dummy","out")[j]
    group,k=divmod(k,s.vcal)
    leaf,slot=divmod(group,18)
    if g.energy(leaf)!=2:
        return None
    prefix=(cell,key,leaf,slot)
    if k<g.ordinary:
        return *prefix,"plain",k+1
    k-=g.ordinary
    if k<44*g.m:
        j,k=divmod(k,44)
        arm=(*prefix,"pair",j)
        if k<2:
            return *arm,("join" if k==0 else "out")
        if k<4:
            return *arm,"pad",k-2
        block,idx=divmod(k-4,20)
        return *arm,"core",block,*core_v(idx)
    j,k=divmod(k-44*g.m,5)
    if k<2:
        return *prefix,"average",j,"input",k
    return *prefix,"average",j,("sum","dummy","out")[k-2]


def nearby(s,p):
    x,y,z=p
    cx,rx=divmod(x,s.px)
    cy,ry=divmod(y,s.py)
    # A long horizontal lane or its one-bond turn encodes edge and owner color in its row.
    colors=set()
    if z==0 and ry>=8:
        colors.add((ry-8)//8)
    # A vertical trunk encodes the same data in its column.
    if z==1 and rx<s.colors:
        colors.add(rx)
    for j in colors:
        if not 0<=j<s.colors:
            continue
        edge=s.edge_by_rank(j//16) if hasattr(s,"edge_by_rank") else edge_unrank(s,j//16)
        if edge is None:
            continue
        ox=j%4
        oy=(j//4)%4
        for i in range(cx-4,cx+2):
            for k in range(cy-1,cy+1):
                if i%4==ox and k%4==oy:
                    yield (i,k),edge
    # The vertical endpoint stubs and their vias also encode an original spin in x.
    if rx>=s.vertex_start:
        idx,sub=divmod(rx-s.vertex_start,8)
        if sub in (3,4,5):
            if hasattr(s,"addresses_at"):
                if idx<s.V:
                    yield from s.addresses_at(((cx,cy),idx))
            else:
                v=vertex_unrank(s,idx,(cx,cy))
                if v is not None:
                    yield from candidates(s.graph,v)


def exchange(s,p,q):
    p,q=tuple(p),tuple(q)
    if len(p)!=3 or len(q)!=3 or p[2] not in (0,1) or q[2] not in (0,1):
        raise ValueError("two cubic-layer lattice points required")
    if sum(abs(x-y) for x,y in zip(p,q))!=1:
        raise ValueError("endpoints must be nearest neighbours")
    addresses=set(nearby(s,p)) | set(nearby(s,q))
    for cell,address in addresses:
        path,sgn=s.path(address,cell)
        for k,(a,b) in enumerate(zip(path,path[1:])):
            if all(min(lo,hi)<=min(x,y)<=max(x,y)<=max(lo,hi) for lo,hi,x,y in zip(a,b,p,q)):
                return sgn if k==getattr(s,"signed_segment",0) else 1
    return 0


def square(point):
    x,y,z=point
    return x-y,x+y+z


def unsquare(point):
    u,v=point
    z=(u+v)%2
    return (u+v-z)//2,(v-u-z)//2,z


def square_exchange(s,p,q):
    if max(abs(x-y) for x,y in zip(p,q))!=1:
        raise ValueError("endpoints must be nearest or diagonal square neighbours")
    a,b=unsquare(p),unsquare(q)
    if sum(abs(x-y) for x,y in zip(a,b))!=1:
        return 0
    return exchange(s,a,b)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ins=ap.add_subparsers(dest="command",required=True)
    for name,n in (("slab",6),("square",4)):
        t=ins.add_parser(name)
        t.add_argument("coordinates",type=int,nargs=n)
    ins.add_parser("measured")
    args=ap.parse_args()
    s=Slab()
    if args.command=="measured":
        v=(s.vertex_start+4,0,0)
        result={"slab":v,"square":square(v),"slab_lag_vector":(0,4*s.py,0),
                "square_lag_vector":(-4*s.py,4*s.py)}
    elif args.command=="slab":
        result=exchange(s,args.coordinates[:3],args.coordinates[3:])
    else:
        result=square_exchange(s,args.coordinates[:2],args.coordinates[2:])
    print(json.dumps(result))


if __name__=="__main__":
    main()

