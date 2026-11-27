"""Unit-exchange zero-field Ising graph. Print any of its periodic microscopic edges."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from fractions import Fraction as F
from functools import lru_cache
import argparse
import json

from model import Magnet


class IsingGraph:
    def __init__(self):
        self.model = Magnet()
        self.p = self.model.table.alphabet.bit_length()-1
        assert self.model.table.alphabet == 1 << self.p
        self.k = 2*self.p
        self.gates = self.k-1
        self.patterns = 1 << self.gates
        self.cell_size = self.p + 81*15*self.gates*self.patterns
        flag = sum(1 << self.model.table.flag_shift(d) for d in (-1,0,1))
        b, I = self.model.b, self.model.I
        self.flip = ((flag*b+1)*b+1)*I
        self.pivot = (self.flip & -self.flip).bit_length()-1

    def measured(self, symbol):
        return self.model.table.spin(self.model.unpack(symbol)[0])

    def logical(self, visible):
        """Site bijection with microscopic visible bit 0 equal to the wave spin."""
        if not 0 <= visible < 1 << self.p:
            raise ValueError("visible word outside alphabet")
        negative = visible & 1
        invariant = (visible >> 1) ^ (((1 << (self.p-1))-1) if negative else 0)
        low = (1 << self.pivot)-1
        rep = (invariant & low) | ((invariant & ~low) << 1)
        observed_negative = self.measured(rep) < 0
        return rep ^ self.flip if negative != observed_negative else rep

    @lru_cache(maxsize=32)
    def target_energy(self, direction, pattern):
        """Choose the representative with positive first spin for k-1 adjacent products."""
        if not 0 <= pattern < self.patterns:
            raise ValueError("pattern outside graph")
        visible = 0
        bit = 0
        for i in range(self.gates):
            bit ^= (pattern >> i) & 1
            visible |= bit << (i+1)
        mask = (1 << self.p)-1
        u, v = self.logical(visible & mask), self.logical(visible >> self.p)
        return self.model.horizontal(u,v) if direction == "east" else self.model.vertical(u,v)

    def edge(self, direction, pattern, copy, gate, kind, star, slot, half):
        if direction not in ("east","north") or kind not in (0,1) or half not in (0,1):
            raise ValueError("unknown direction, factor kind or path half")
        maximum = 4 if direction == "east" else 11
        if not (0 <= pattern < self.patterns and 1 <= copy <= maximum and
                0 <= gate < self.gates and 0 <= star < 8 and 0 <= slot < 4):
            raise ValueError("graph coordinate outside its range")
        owner = (0,0)
        neighbor = (1,0) if direction == "east" else (0,1)
        loop = (direction,pattern,copy)
        def visible(j):
            return (owner if j < self.p else neighbor, "visible", j % self.p)
        ti = (owner,"loop",*loop,gate)
        tn = (owner,"loop",*loop,(gate+1)%self.gates)
        center = (owner,"star",*loop,gate,kind,star)
        middle = (owner,"middle",*loop,gate,kind,star,slot)
        if half == 0:
            return center, middle, 1
        terminal = (ti, tn, ti, ti)[slot] if kind == 0 else (ti, tn, visible(gate), visible(gate+1))[slot]
        epsilon = star | ((star.bit_count()%2) << 3)
        sign = 1-2*((epsilon >> slot)&1)
        if slot == 0:
            flux = -1 if gate == 0 and copy <= self.target_energy(direction,pattern) else 1
            control = (1-2*((pattern >> gate)&1)) if kind else 1
            sign *= -flux*control
        return middle, terminal, sign


def exp_bounds(x):
    """Positive rational Taylor sum with geometric remainder; x is in [0,4]."""
    assert 0 <= x <= 4
    term = total = F(1)
    for j in range(1,65):
        term *= x/j
        total += term
    return total, total + term*x/65 / (1-x/66)


def effective_z_from_exp(r, gates):
    # Each intermediate is monotone on this branch, r=e^(2b) >= 1.
    c = (r + 1/r)/2
    x = (c + 1/c)/2
    strength = x**4 / (2*x*x-1)
    v = (strength**4-1)/(strength**4+1)
    q = v**gates
    return (1-q)/(1+q)


def effective_z_bounds(beta, gates):
    lo, hi = exp_bounds(2*beta)
    scale = 1 << 50
    lo = F((lo*scale).__floor__(), scale)
    hi = F((hi*scale).__ceil__(), scale)
    return effective_z_from_exp(hi,gates), effective_z_from_exp(lo,gates)


def find_endpoint(gates, low_z, high_z):
    lo, hi = F(0), F(2)
    for _ in range(64):
        mid = (lo+hi)/2
        lower, upper = effective_z_bounds(mid,gates)
        if low_z < lower <= upper < high_z:
            return mid
        if lower >= high_z:
            lo = mid
        elif upper <= low_z:
            hi = mid
        else:
            # The requested band contains an open neighborhood of its midpoint.
            if lower + upper > low_z + high_z:
                lo = mid
            else:
                hi = mid
    raise ArithmeticError("failed to isolate the rational temperature window")


def window(gates):
    return (find_endpoint(gates,F(3,4),F(19,25)), find_endpoint(gates,F(5,8),F(16,25)))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    commands = p.add_subparsers(dest="command",required=True)
    commands.add_parser("describe")
    commands.add_parser("window")
    edge = commands.add_parser("edge")
    edge.add_argument("direction",choices=("east","north"))
    for name in ("pattern","copy","gate","kind","star","slot","half"):
        edge.add_argument(name,type=int)
    args = p.parse_args()
    graph = IsingGraph()
    if args.command == "describe":
        result = {"spins_per_cell":graph.cell_size, "visible":graph.p, "patterns_per_bond":graph.patterns,
                  "gates_per_loop":graph.gates,"spin_values":[-1,1],"exchange_values":[-1,1],"field":0}
    elif args.command == "window":
        result = [str(x) for x in window(graph.gates)]
    else:
        result = graph.edge(args.direction,args.pattern,args.copy,args.gate,args.kind,args.star,args.slot,args.half)
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()

