"""A binary-energy square magnet with a simple leading period-three pole pair."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from fractions import Fraction as F
from functools import lru_cache
import argparse
import json

import local_machine as lm
from binary_pairs import BinaryPairs

DEN=1 << 56
R=DEN >> 6
ANCHOR=DEN >> 7
LONG=DEN >> 14
SHORT=DEN >> 22
PENALTY=1 << 12
DIRECT=DEN >> 48
SETUP=DEN >> 51
PROGRAM=DEN >> 56
START=("orbit",-1,False,False)
FIXED=("fixed",)


def basis_steps():
    # Expected resident, move, written resident. Six setup and seven erasure steps total.
    return ((lm.EMPTY,1,lm.BIT),(lm.EMPTY,1,lm.BIT),(lm.EMPTY,1,lm.BIT),
            (lm.EMPTY,-1,lm.BIT),(lm.BIT,-1,lm.BIT),(lm.BIT,-1,lm.BIT),
            (lm.BIT,1,lm.EMPTY),(lm.BIT,1,lm.EMPTY),(lm.BIT,1,lm.EMPTY),
            (lm.BIT,-1,lm.EMPTY),(lm.EMPTY,-1,lm.EMPTY),(lm.EMPTY,-1,lm.EMPTY),
            (lm.EMPTY,0,lm.EMPTY))


class BinaryWave(BinaryPairs):
    def __init__(self):
        super().__init__()
        self.I=2*DEN
        self.size=self.g*self.b**2*self.I
        self.extra=[FIXED,*[("baseline",i) for i in range(1,13) if i!=6],
                    *[("long",d,g) for d in (-1,1) for g in (False,True)],
                    *[(phase,d) for d in (-1,1) for phase in ("short-prep","short-move")]]
        first=max(self.table.ids.values())+1
        self.ids={**self.table.ids,**{s:first+i for i,s in enumerate(self.extra)}}
        assert max(self.ids.values()) < 1 << self.table.payload_bits
        self.baseline_schedule=basis_steps()

    def head(self,state,d):
        return (self.ids[state] << lm.PAYLOAD_SHIFT) | (1 << self.table.flag_shift(d))

    def actions(self,state,raw):
        memory=lm.plain(raw)
        if state==lm.D or state==FIXED or state[0]=="baseline":
            k=0 if state==lm.D else (6 if state==FIXED else state[1])
            expected,move,write=self.baseline_schedule[k]
            if memory!=expected:
                return
            if state==lm.D:
                yield lm.D,0,lm.EMPTY,DIRECT
            if state==FIXED:
                yield FIXED,0,lm.BIT,ANCHOR
            target=FIXED if k==5 else (lm.B if k==12 else ("baseline",k+1))
            yield target,move,write,SETUP
            return
        if memory not in (lm.EMPTY,lm.LEFT,lm.RIGHT,lm.GAIN,lm.HEAT):
            return
        penalty=PENALTY if memory!=lm.EMPTY else 1
        anchor=memory==lm.LEFT and (state==START or state[0]=="long" and state[1]==-1
                                    or state==("short-prep",-1))
        if anchor:
            yield START,0,lm.LEFT,ANCHOR
            yield ("erase_right",),1,lm.LEFT,PROGRAM
            yield ("long",1,False),1,lm.LEFT,LONG//penalty
            yield ("short-move",1),0,lm.LEFT,-SHORT//penalty
        elif state[0]=="long":
            _,d,gain=state
            if memory==lm.RIGHT:
                d,gain=-1,True
            elif memory==lm.GAIN:
                gain=d==1
            yield ("long",d,gain),d,memory,(2 if gain else 1)*LONG//penalty
        elif state[0]=="short-prep":
            d=-1 if memory==lm.HEAT else state[1]
            yield ("short-move",d),0,memory,SHORT//penalty
        elif state[0]=="short-move":
            d=state[1]
            yield ("short-prep",d),d,memory,SHORT//penalty

    def terms(self):
        for a,left,center,right,weight in self.table.terms():
            if a==self.base or a>=16 and (a >> lm.PAYLOAD_SHIFT) in self.orbit:
                continue
            if a<16:
                c=R
            else:
                c=PROGRAM*(weight[0] if center==self.terminal and not left and not right else 1)
            yield a,left,center,right,c*(1-2*lm.quadratic(left|right))
        for state in (lm.D,START,*self.extra):
            for raw in lm.MEMORIES:
                for target,move,written,c in self.actions(state,raw):
                    lane=1 | (self.ids[target] << 1)
                    left=lane if move==-1 else 0
                    right=lane if move==1 else 0
                    center=lm.next_memory(raw,written) | (self.head(target,0) if move==0 else 0)
                    for incoming in ((0,) if state==lm.D else (-1,0,1)):
                        yield raw | self.head(state,incoming),left,center,right,c*(1-2*lm.quadratic(left|right))

    @lru_cache(maxsize=16)
    def zero_count(self,l,y,r,v):
        if not (0<=l<self.b and 0<=r<self.b and 0<=y<self.g and 0<=v<self.g):
            raise ValueError("binary wave row coordinate outside alphabet")
        n=DEN
        for a,left,center,right,c in self.terms():
            parity=((a&v) ^ (left&l) ^ (center&y) ^ (right&r)).bit_count()%2
            n+=(1-2*parity)*c
        assert 0<n<self.I
        return n

    def describe(self):
        count=norm=0
        for *_,c in self.terms():
            count+=1
            norm+=abs(c)
        return {"dimension":2,"alphabet":self.size,"bits":self.size.bit_length()-1,"index":self.I,
                "east_and_north_energies":[0,1],"beta_window":["1/4","1/2"],
                "scattering_options":count,"absolute_coefficient_sum":str(F(norm,DEN))}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    sub=p.add_subparsers(dest="command",required=True)
    sub.add_parser("describe")
    for name in ("horizontal","vertical"):
        c=sub.add_parser(name)
        c.add_argument("old",type=int)
        c.add_argument("new",type=int)
    s=sub.add_parser("spin")
    s.add_argument("ordinal",type=int)
    r=sub.add_parser("row")
    for name in ("left","center","right","child"):
        r.add_argument(name,type=int)
    args=p.parse_args()
    model=BinaryWave()
    if args.command=="describe":
        result=model.describe()
    elif args.command=="spin":
        result=model.spin(args.ordinal)
    elif args.command=="row":
        n=model.zero_count(args.left,args.center,args.right,args.child)
        result=[n,model.I-n]
    else:
        result=getattr(model,args.command)(args.old,args.new)
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()

