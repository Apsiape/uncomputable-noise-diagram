"""Two square-lattice pair tables with only energies zero and one."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from fractions import Fraction as F
from functools import lru_cache
import argparse
import json

import local_machine as lm

# All entries in the coefficient table have common denominator H.
H=1 << 70
RESIDENT=H >> 6
ADVANCE=H >> 12
COLLISION=1 << 12
BASE=H >> 63
WORK=H >> 67
HOLD=H >> 70


class BinaryPairs:
    def __init__(self):
        self.table=lm.Table()
        self.b=self.table.lane_size
        self.g=self.table.group_size
        self.I=2*H
        self.size=self.g*self.b**2*self.I
        self.orbit={self.table.ids[s] for s in lm.ORBIT}
        self.base=self.table.head(lm.D,0)
        self.terminal=self.table.head(lm.B,0)

    def terms(self):
        for a,left,center,right,(units,power,zpower,den) in self.table.terms():
            resident=a & 15
            if a<16:
                coefficient=RESIDENT
            elif a==self.base:
                coefficient=BASE
            elif (a >> lm.PAYLOAD_SHIFT) in self.orbit and units in (4,8):
                if left or right:
                    coefficient=ADVANCE*(units//4)
                    if resident:
                        coefficient//=COLLISION
                elif lm.plain(resident)==lm.LEFT:
                    coefficient=HOLD
                else:
                    continue
            else:
                coefficient=WORK*(units if center==self.terminal and not left and not right else 1)
            correction=1-2*lm.quadratic(left|right)
            yield a,left,center,right,coefficient*correction

    def unpack(self,i):
        if not 0<=i<self.size:
            raise ValueError("binary-pair symbol outside alphabet")
        w,index=divmod(i,self.I)
        w,r=divmod(w,self.b)
        y,l=divmod(w,self.b)
        return y,l,r,index

    def horizontal(self,west,east):
        y,_,r,_=self.unpack(west)
        v,l,_,_=self.unpack(east)
        return lm.quadratic((l^self.table.lane(y,-1)) | ((r^self.table.lane(v,1))*self.b))

    @lru_cache(maxsize=16)
    def zero_count(self,l,y,r,v):
        if not (0<=l<self.b and 0<=r<self.b and 0<=y<self.g and 0<=v<self.g):
            raise ValueError("binary row coordinate outside alphabet")
        n=H
        for a,left,center,right,c in self.terms():
            parity=((a&v) ^ (left&l) ^ (center&y) ^ (right&r)).bit_count()%2
            n+=(1-2*parity)*c
        assert 0<n<self.I
        return n

    def vertical(self,south,north):
        y,l,r,_=self.unpack(south)
        v,_,_,index=self.unpack(north)
        return int(index>=self.zero_count(l,y,r,v))

    def spin(self,ordinal):
        return self.table.spin(self.unpack(ordinal)[0],lm.MASS)

    def describe(self):
        terms=tuple(self.terms())
        return {"alphabet":self.size,"bits":self.size.bit_length()-1,"index":self.I,
                "energies":[0,1],"dimension":2,"range":"east and north nearest neighbours",
                "scattering_options":len(terms),"absolute_coefficient_sum":str(F(sum(abs(t[-1]) for t in terms),H)),
                "beta_window":["1/4","1/2"]}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    sub=p.add_subparsers(dest="command",required=True)
    sub.add_parser("describe")
    for name in ("horizontal","vertical"):
        cmd=sub.add_parser(name)
        cmd.add_argument("old",type=int)
        cmd.add_argument("new",type=int)
    spin=sub.add_parser("spin")
    spin.add_argument("ordinal",type=int)
    row=sub.add_parser("row")
    for field in ("left","center","right","child"):
        row.add_argument(field,type=int)
    args=p.parse_args()
    m=BinaryPairs()
    if args.command=="describe":
        val=m.describe()
    elif args.command=="spin":
        val=m.spin(args.ordinal)
    elif args.command=="row":
        n=m.zero_count(args.left,args.center,args.right,args.child)
        val=[n,m.I-n]
    else:
        val=getattr(m,args.command)(args.old,args.new)
    print(json.dumps(val,indent=2))


if __name__=="__main__":
    main()

