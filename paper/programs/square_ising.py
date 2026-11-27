"""Practical coordinate lookup for the signed square-lattice Ising model."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from bisect import bisect_right
import argparse
import json
from herald_ising import HeraldGraph,z_at_y
from herald_blocks import block
from cubic_slab import Slab
from slab_lookup import square,exchange,square_exchange


class CircuitSlab(Slab):
    signed_segment=1  # The first interlayer via is private to this edge.
    def __init__(self,graph=None):
        self.graph=HeraldGraph() if graph is None else graph
        self.V,self.E=self.graph.V,self.graph.E
        self.set_geometry()

    def parent_z(self,y):
        return z_at_y(y,self.graph.W)

    def erank(self,address):
        mod,i=address
        return self.graph.estarts[mod]+i

    def vrank(self,v):
        return v[1]

    def port(self,v,y,a,first):
        return self.graph.port(v,y,a,first)

    def edge_by_rank(self,i):
        m=bisect_right(self.graph.estarts,i)-1
        return m,i-self.graph.estarts[m]

    def addresses_at(self,v):
        g=self.graph
        (cx,cy),x=v
        if x>=g.base:
            m=bisect_right(g.vstarts,x)-1
            for k in block(g.word(m)).incidences[x-g.vstarts[m]]:
                yield (cx,cy),(m,k)
            return
        def tagged(ij):
            return [3*m for m in g.users(-1-ij)]
        here=(cx,cy)
        homes=[]
        if x<2*g.p:
            if x in (0,2*g.p-1):
                j=0
            else:
                j=(x+1)//2
            for r,(dx,dy) in enumerate(((0,0),(1,0),(0,1))):
                owner=here if x==2*g.p-1 else (cx-dx,cy-dy)
                homes.extend((owner,m) for m in tagged(r*g.p+j))
        elif x<g.loop:
            homes=[(here,m) for m in tagged(3*g.p+(x-2*g.p)//2)]
        elif x<g.rail:
            j=x-g.loop
            ms=[3*i+2 for i in (j-1,j) if 0<=i<g.W]
            if j in (0,g.W):
                ms.append(3*g.W)
            homes=[(here,m) for m in ms]
        elif x<g.herald:
            j=(x-g.rail)//2
            ms=[3*j,*[3*k for k in g.users(j)]]
            if j==g.W-1:
                ms.append(3*g.W)
            homes=[(here,m) for m in ms]
        elif x<g.chain:
            j=(x-g.herald)//2
            homes=[(here,3*j+h) for h in range(3)]
        else:
            j=x-g.chain
            ms=[3*g.W+1+i for i in (j-1,j) if 0<=i<2*g.W+1]
            if j in (0,2*g.W+1):
                ms.extend(tagged(3*g.p+7))
            homes=[(here,m) for m in ms]
        for (ox,oy),m in homes:
            slots,w=g.module(m)
            for s,k in block(w).slot_edges.items():
                (dx,dy),i=slots[s]
                if (ox+dx,oy+dy,i)==(cx,cy,x):
                    yield (ox,oy),(m,k)

    def describe(self):
        result=super().describe()
        result.update({"in_square_unit_cell":32*self.px*self.py,"original_spins_per_abstract_cell":self.V,
                       "original_edges_per_abstract_cell":self.E,"maximum_active_coordination":3,
                       "negative_bonds":"matching of interlayer rungs","signed_path_segment_zero_based":1,
                       "square_observed_site":square((self.vertex_start+4,0,0)),
                       "square_lag_vector":[-4*self.py,4*self.py]})
        return result


def main():
    p=argparse.ArgumentParser(description=__doc__)
    subs=p.add_subparsers(dest="command",required=True)
    subs.add_parser("describe")
    for n,k in (("square",4),("slab",6)):
        b=subs.add_parser(n)
        b.add_argument("coord",type=int,nargs=k)
    t=subs.add_parser("path")
    t.add_argument("module",type=int)
    t.add_argument("local",type=int)
    t.add_argument("--cell",nargs=2,type=int,default=[0,0])
    args=p.parse_args()
    s=CircuitSlab()
    if args.command=="describe":
        res=s.describe()
    elif args.command=="path":
        res=s.path((args.module,args.local),args.cell)
    elif args.command=="square":
        res=square_exchange(s,args.coord[:2],args.coord[2:])
    else:
        res=exchange(s,args.coord[:3],args.coord[3:])
    print(json.dumps(res,indent=2))


if __name__=="__main__":
    main()

