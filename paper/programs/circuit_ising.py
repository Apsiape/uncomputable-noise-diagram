"""Print unit Ising edges in the circuit-sized periodic cell; finite integer lookup."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from fractions import Fraction as F
from functools import lru_cache
import argparse
import json

from bond_circuit import FUNCTIONS, PADDED, compile_bond
from ising import IsingGraph


@lru_cache(maxsize=16)
def coefficients(function):
    """Integer Walsh coefficients of 8 times the gate-correct indicator."""
    coeff = [0]*8
    for a in (0,1):
        for b in (0,1):
            out = (function >> (2*a+b))&1
            assignment = a | (b << 1) | (out << 2)
            for mask in range(8):
                coeff[mask] += 1-2*((assignment & mask).bit_count()%2)
    return tuple(coeff)


def factors(function, roles, t, following, dangling, divisor=1):
    """Signed eight-terminal parity factors, before attaching even padding."""
    cs = coefficients(function)
    result = []
    for mask,c in enumerate(cs):
        word = tuple(spin for k,pair in enumerate(roles) if mask & (1 << k) for spin in pair)
        complement = (8 if mask == 0 else 0)-c
        for n,slots in ((c,word),(c,(t,following)+word),(complement,(dangling,t)+word)):
            if slots and n:
                assert n%divisor==0
                result.extend([(1 if n>0 else -1,slots)]*(abs(n)//divisor))
    return result


def structural_counts(divisor=1,centers=8):
    # Distinct slots give the same size as repeated named terminals.
    roles = [(0,1),(2,3),(4,5)]
    counts = {}
    for fun in FUNCTIONS:
        fs = factors(fun,roles,6,7,8,divisor)
        counts[fun] = (len(fs),sum(10+3*centers+int(len(x)<8) for _,x in fs))
    return counts


class CircuitGraph:
    gate_count = PADDED
    centers = 8
    divisor = 1
    degree_bound = 720
    maxima = {"east":4,"north":11}

    def __init__(self):
        self.parent = IsingGraph()

    def compile(self,direction,threshold,patterns=(),wanted=None,consumer=None):
        return compile_bond(self.parent,direction,threshold,patterns,wanted,consumer)

    @lru_cache(maxsize=32)
    def gate(self,direction,threshold,index):
        return self.compile(direction,threshold,wanted=index)

    def gate_factors(self,direction,threshold,index):
        owner = (0,0)
        other = (1,0) if direction=="east" else (0,1)
        prefix = (owner,direction,threshold)
        def pair(source):
            if source >= 0:
                return tuple((*prefix,"rail",source,k) for k in (0,1))
            i = -source-1
            return tuple((owner if j<self.parent.p else other,"visible",j%self.parent.p)
                         for j in (i,i+1))
        def loop(i):
            return (*prefix,"loop",i)
        if index == self.gate_count:
            return [(1,(loop(self.gate_count),loop(0))+pair(self.gate_count-1))]*(8//self.divisor)
        fun,a,b = self.gate(direction,threshold,index)
        return factors(fun,(pair(a),pair(b),pair(index)),loop(index),loop(index+1),
                       (*prefix,"dangling",index),self.divisor)

    def edge(self,direction,threshold,index,ordinal,kind,*parts):
        maximum = self.maxima[direction]
        if not 1 <= threshold <= maximum or not 0 <= index <= self.gate_count:
            raise ValueError("bond, threshold or gate outside its range")
        fs = self.gate_factors(direction,threshold,index)
        if not 0 <= ordinal < len(fs):
            raise ValueError("factor index outside this gate")
        sign,external = fs[ordinal]
        prefix = ((0,0),direction,threshold,"factor",index,ordinal)
        def inside(k):
            return (*prefix,"inside",k)
        if kind=="port" and len(parts)==1 and 0 <= parts[0] < 8:
            i = parts[0]
            endpoint = external[i] if i<len(external) else (*prefix,"pad")
            return endpoint,inside(i),1
        if kind!="star" or len(parts)!=3:
            raise ValueError("use port SLOT or star BLOCK CENTER SLOT")
        block,center,slot = parts
        if not (0 <= block < 3 and 0 <= center < self.centers and 0 <= slot < 4):
            raise ValueError("star address out of range")
        first,second = (*prefix,"connector",0),(*prefix,"connector",1)
        blocks = ((inside(0),inside(1),inside(2),first),
                  (first,inside(3),inside(4),second),
                  (second,inside(5),inside(6),inside(7)))
        epsilon = center | ((center.bit_count()%2) << 3)
        bond_sign = 1-2*((epsilon >> slot)&1)
        if slot==0:
            bond_sign *= -sign if block==0 else -1
        return (*prefix,"star",block,center),blocks[block][slot],bond_sign

    def describe(self):
        sizes = structural_counts(self.divisor,self.centers)
        total = self.parent.p
        edges = 0
        details = {}
        for direction,maximum in self.maxima.items():
            raw_counts = []
            for j in range(1,maximum+1):
                raw,stats,_ = self.compile(direction,j)
                raw_counts.append(raw)
                total += 4*self.gate_count+1+(8//self.divisor)*(11+3*self.centers)+sum(n*sizes[f][1] for f,n in stats.items())
                edges += (8+12*self.centers)*(8//self.divisor+sum(n*sizes[f][0] for f,n in stats.items()))
            details[direction]=raw_counts
        return {"spins_per_cell":total,"edges_per_cell":edges,"maximum_degree_bound":self.degree_bound,"gate_count_per_threshold":self.gate_count,
                "before_padding":details,"energy":"-sign*spin_u*spin_v","exchange_magnitudes":[1],
                "fields":0,"window":[str(x) for x in window(self.gate_count,self.centers,self.divisor)]}


def power_bounds(value, exponent, bits=95):
    """Outward fixed-point binary powering on [0,1], including very large exponents."""
    scale = 1 << bits
    low = (value.numerator*scale)//value.denominator
    high = -((-value.numerator*scale)//value.denominator)
    a=b=scale
    while exponent:
        if exponent & 1:
            a,b = a*low//scale,(b*high+scale-1)//scale
        low,high = low*low//scale,(high*high+scale-1)//scale
        exponent >>= 1
    return F(a,scale),F(b,scale)


def z_at_exponential(r,gate_count,centers=8,divisor=1):
    c = (r+1/r)/2
    e4 = c**4/(2*c*c-1)
    strength_squared=e4**(centers//4)
    v=((strength_squared-1)/(strength_squared+1))**3 * ((r-1)/(r+1))**8
    thermal=((1+v)/(1-v))**(4//divisor)
    p = thermal/(1+thermal)
    t = (thermal**2-1)/(thermal**2+1)
    # q = t (p*t)^W
    qlo,qhi = power_bounds(p*t,gate_count)
    return (1-t*qhi)/(1+t*qhi),(1-t*qlo)/(1+t*qlo)


def effective_z_bounds(b,gate_count=PADDED,centers=8,divisor=1):
    x = 2*b
    assert 0 <= x <= 10
    term=total=F(1)
    for i in range(1,101):
        term *= x/i
        total += term
    upper = total+term*x/101/(1-x/102)
    scale=1 << 70
    lo=F((total*scale).__floor__(),scale)
    hi=F((upper*scale).__ceil__(),scale)
    return z_at_exponential(hi,gate_count,centers,divisor)[0],z_at_exponential(lo,gate_count,centers,divisor)[1]


def window(gate_count=PADDED,centers=8,divisor=1):
    result=[]
    for lower,upper in ((F(3,4),F(19,25)),(F(5,8),F(16,25))):
        lo,hi=F(0),F(5)
        for _ in range(80):
            mid=(lo+hi)/2
            a,b=effective_z_bounds(mid,gate_count,centers,divisor)
            if lower<a<=b<upper:
                result.append(mid)
                break
            if a+b>lower+upper:
                lo=mid
            else:
                hi=mid
        else:
            raise ArithmeticError("could not bracket circuit temperature")
    return tuple(result)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    subs=p.add_subparsers(dest="command",required=True)
    subs.add_parser("describe")
    subs.add_parser("window")
    for name in ("gate","edge"):
        sub=subs.add_parser(name)
        sub.add_argument("direction",choices=("east","north"))
        for field in ("threshold","index"):
            sub.add_argument(field,type=int)
        if name=="edge":
            sub.add_argument("factor",type=int)
            sub.add_argument("kind",choices=("port","star"))
            sub.add_argument("parts",nargs="+",type=int)
    args=p.parse_args()
    graph=CircuitGraph()
    if args.command=="describe":
        result=graph.describe()
    elif args.command=="window":
        result=[str(v) for v in window()]
    elif args.command=="gate":
        result=graph.gate(args.direction,args.threshold,args.index)
    else:
        result=graph.edge(args.direction,args.threshold,args.index,args.factor,args.kind,*args.parts)
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()

