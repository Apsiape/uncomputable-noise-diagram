"""A circuit-sized zero-field Ising realization of the two binary parent tables."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from collections import defaultdict
from functools import lru_cache
import argparse
import json

import local_machine as lm
import binary_wave as bw
from bond_circuit import Wire,Emitter,GateFound,Columns,Parities,COPY,XOR,AND,NOT,parent_word
from circuit_ising import CircuitGraph
from ising import IsingGraph


class Encoding(IsingGraph):
    def __init__(self):
        self.model=bw.BinaryWave()
        self.p=self.model.size.bit_length()-1
        self.gates=2*self.p-1
        self.patterns=1 << self.gates
        flag=sum(1 << self.model.table.flag_shift(d) for d in (-1,0,1))
        self.flip=((flag*self.model.b+1)*self.model.b+1)*self.model.I
        self.pivot=(self.flip & -self.flip).bit_length()-1

    def measured(self,symbol):
        return self.model.spin(symbol)

    @lru_cache(maxsize=1)
    def profiles(self):
        # Factor each Walsh monomial into low memory/flag and high payload characters.
        rows=defaultdict(list)
        for a,l,center,r,c in self.model.terms():
            if l:
                dest,out="left",l >> 1
            elif r:
                dest,out="right",r >> 1
            elif a>=16:
                dest,out="center",center >> 7
            else:
                dest,out="passive",0
            low=(a&127) | ((center&15) << 7)
            if dest!="passive":
                low |= 1 << {"center":11,"left":12,"right":13}[dest]
            rows[dest,a >> 7,out,abs(c)].append((low,1 if c>0 else -1))
        profiles=defaultdict(list)
        for (dest,src,out,c),terms in rows.items():
            terms.sort()
            orientation=terms[0][1]
            profile=tuple((mask,sign*orientation) for mask,sign in terms)
            profiles[dest,c,profile].append((src,out,orientation))
        return tuple((dest,c,low,tuple(high)) for (dest,c,low),high in profiles.items())


def conditional_xor(e,a,b):
    if a is e.zero:
        return b
    if b is e.zero:
        return a
    if a is b:
        return e.zero
    return e.op(XOR,a,b)


def population(e,items):
    if len(items)==1:
        return [items[0]]
    counts=Columns(e,len(items).bit_length())
    for bit in items:
        counts.add(0,bit)
    return counts.finish()


class SignedSum:
    def __init__(self,e,width,offset):
        self.e=e
        self.width=width
        self.offset=offset
        self.columns=Columns(e,width)

    def add(self,bit,coefficient):
        if bit is self.e.zero:
            return
        if bit is self.e.one:
            self.offset+=coefficient
            return
        if coefficient<0:
            self.offset+=coefficient
            bit=self.e.op(NOT,bit)
            coefficient=-coefficient
        coefficient %= 1 << self.width
        while coefficient:
            low=coefficient & -coefficient
            self.columns.add(low.bit_length()-1,bit)
            coefficient-=low

    def top(self):
        for i in range(self.width):
            if (self.offset >> i)&1:
                self.columns.add(i,self.e.one)
        return self.columns.finish()[-1]


def parts(graph,words):
    idx_bits=graph.model.I.bit_length()-1
    lane=graph.model.table.width
    return words[:idx_bits],words[idx_bits:idx_bits+lane],words[idx_bits+lane:idx_bits+2*lane],words[-20:]


def horizontal(e,graph,a,b):
    _,r,_,old=parts(graph,a)
    _,_,l,new=parts(graph,b)
    west=[old[graph.model.table.flag_shift(-1)],*old[7:]]
    east=[new[graph.model.table.flag_shift(1)],*new[7:]]
    diff=[e.op(XOR,u,v) for u,v in zip(l+r,west+east,strict=True)]
    parity=e.zero
    for i in range(0,len(diff),2):
        parity=conditional_xor(e,parity,e.op(AND,diff[i],diff[i+1]))
    return parity


def vertical(e,graph,a,b):
    _,r,l,old=parts(graph,a)
    index,_,_,child=parts(graph,b)
    low_pool=Parities(e,[*child[:7],*old[:4],old[5],l[0],r[0]])
    src_pool=Parities(e,child[7:])
    dest_pool={d:Parities(e,bits) for d,bits in (("left",l[1:]),("right",r[1:]),
                                                 ("center",old[7:]),("passive",[]))}
    summed=SignedSum(e,len(index)+1,-bw.DEN)
    for i,bit in enumerate(index):
        summed.add(bit,1 << i)
    lows,highs={},{}
    for dest,c,profile,high in graph.profiles():
        if profile not in lows:
            lowbits=[]
            for mask,sign in profile:
                bit=low_pool.get(mask)
                lowbits.append(bit if sign==1 else e.op(NOT,bit))
            lows[profile]=population(e,lowbits)
        key=dest,high
        if key not in highs:
            highbits=[]
            for src,out,sign in high:
                bit=conditional_xor(e,src_pool.get(src),dest_pool[dest].get(out))
                highbits.append(bit if sign==1 else e.op(NOT,bit))
            highs[key]=population(e,highbits)
        x,y=lows[profile],highs[key]
        n,m=len(profile),len(high)
        summed.offset-=c*n*m
        # -(n-2x)(m-2y)c, where x and y count negative low and high signs.
        for i,bit in enumerate(x):
            summed.add(bit,2*c*m << i)
        for j,bit in enumerate(y):
            summed.add(bit,2*c*n << j)
        for i,u in enumerate(x):
            for j,v in enumerate(y):
                if u is not e.zero and v is not e.zero:
                    cross=e.op(AND,u,v)
                    summed.add(cross,-(4*c << (i+j)))
    return e.op(NOT,summed.top())


class SmallEmitter(Emitter):
    def acquire(self,wire):
        # Five consumers and one COPY exhaust a wire's degree-six fanout.
        if wire.uses==5:
            wire.end=self.emit(COPY,wire.end,wire.end)
            wire.uses=0
        wire.uses+=1
        return wire.end


class SmallGraph(CircuitGraph):
    gate_count=66838
    centers=4
    divisor=2
    degree_bound=48
    maxima={"east":1,"north":1}

    def __init__(self):
        self.parent=Encoding()

    def compile(self,direction,threshold,patterns=(),wanted=None,consumer=None):
        if direction not in self.maxima or threshold!=1 or wanted is not None and not 0<=wanted<self.gate_count:
            raise ValueError("unknown circuit or gate")
        try:
            e=SmallEmitter(self.parent.gates,patterns,wanted,consumer)
            inputs=[Wire(e.emit(COPY,x.end,x.end),x.value) for x in e.inputs]
            physical=[e.zero]
            for bit in inputs:
                physical.append(e.op(XOR,physical[-1],bit))
            p=self.parent.p
            a,b=(parent_word(e,self.parent,w,lm.MASS) for w in (physical[:p],physical[p:]))
            output=(horizontal if direction=="east" else vertical)(e,self.parent,a,b)
            raw=e.count
            assert raw<=self.gate_count and output.end==raw-1,(raw,self.gate_count)
            if consumer is not None:
                if raw-1<=consumer<self.gate_count-1:
                    e.found_consumers.append(consumer+1)
                return tuple(e.found_consumers)
            if wanted is not None:
                return COPY,wanted-1,wanted-1
            stats=dict(e.stats)
            stats[COPY]+=self.gate_count-raw
            return raw,stats,output.value
        except GateFound as found:
            return found.gate


def main():
    p=argparse.ArgumentParser(description=__doc__)
    cmds=p.add_subparsers(dest="command",required=True)
    cmds.add_parser("describe")
    ed=cmds.add_parser("edge")
    ed.add_argument("direction",choices=("east","north"))
    for name in ("gate","factor"):
        ed.add_argument(name,type=int)
    ed.add_argument("kind",choices=("star","port"))
    ed.add_argument("parts",nargs="+",type=int)
    args=p.parse_args()
    graph=SmallGraph()
    result=(graph.describe() if args.command=="describe" else
            graph.edge(args.direction,1,args.gate,args.factor,args.kind,*args.parts))
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()

