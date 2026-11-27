"""Stream a bounded-fanout Boolean circuit for either parent-bond threshold."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from collections import Counter
from math import comb

import local_machine as lm
from ising import IsingGraph

ZERO, NOT, XOR, AND, COPY, OR, ONE = 0, 3, 6, 8, 12, 14, 15
FUNCTIONS = {ZERO:"zero", NOT:"not", XOR:"xor", AND:"and", COPY:"copy", OR:"or", ONE:"one"}
# All thresholds use precisely this many thermally tested gates, including copies.
PADDED = 1 << 22


class Wire:
    __slots__ = ("end", "value", "uses")

    def __init__(self, end, value):
        self.end = end
        self.value = value
        self.uses = 0


class GateFound(Exception):
    def __init__(self, gate):
        self.gate = gate


class Emitter:
    """Keep only live wires. Optional bit-parallel lanes evaluate ideal circuits."""
    def __init__(self, width, patterns=(), wanted=None, consumer=None):
        self.wanted = wanted
        self.consumer = consumer
        self.found_consumers = []
        self.count = 0
        self.stats = Counter()
        self.universe = (1 << len(patterns))-1
        self.inputs = [Wire(-i-1, sum(((x >> i)&1) << j for j,x in enumerate(patterns)))
                       for i in range(width)]
        self.zero = Wire(self.emit(ZERO,-1,-1), 0)
        self.one = Wire(self.emit(ONE,-1,-1), self.universe)

    def emit(self, function, a, b):
        i = self.count
        if self.consumer is not None and function not in (ZERO,ONE):
            if a == self.consumer or (function not in (COPY,NOT) and b == self.consumer):
                self.found_consumers.append(i)
        if i == self.wanted:
            raise GateFound((function,a,b))
        self.count += 1
        self.stats[function] += 1
        return i

    def acquire(self, wire):
        source = wire.end
        wire.end = self.emit(COPY,source,source)
        return source

    def op(self, function, a, b=None):
        left = self.acquire(a)
        right = left if b is None else self.acquire(b)
        gate = self.emit(function,left,right)
        if function == COPY:
            value = a.value
        elif function == NOT:
            value = self.universe ^ a.value
        elif function == XOR:
            value = a.value ^ b.value
        elif function == AND:
            value = a.value & b.value
        elif function == OR:
            value = a.value | b.value
        else:
            raise ValueError(function)
        return Wire(gate,value)

    def full_adder(self,a,b,c):
        x = self.op(XOR,a,b)
        y = self.op(AND,a,b)
        return self.op(XOR,x,c), self.op(OR,y,self.op(AND,x,c))

    def majority(self,a,b,c):
        return self.op(OR,self.op(AND,a,b),self.op(AND,self.op(XOR,a,b),c))


class Columns:
    """Three binary tokens of one weight become a sum token and a carry."""
    def __init__(self, e, width):
        self.e = e
        self.bits = [[] for _ in range(width)]

    def add(self, pos, bit):
        while pos < len(self.bits):
            bucket = self.bits[pos]
            if len(bucket) < 2:
                bucket.append(bit)
                break
            summed, bit = self.e.full_adder(bucket[0],bucket[1],bit)
            bucket[:] = [summed]
            pos += 1

    def finish(self):
        result = []
        carry = None
        for bucket in self.bits:
            terms = list(bucket)
            if carry is not None:
                terms.append(carry)
            if len(terms) == 3:
                val,carry = self.e.full_adder(*terms)
            elif len(terms) == 2:
                val,carry = self.e.op(XOR,*terms),self.e.op(AND,*terms)
            else:
                val = terms[0] if terms else self.e.zero
                carry = None
            result.append(val)
        return result


class Parities:
    def __init__(self,e,bits):
        self.e = e
        self.cache = {0:e.zero, **{1 << i:b for i,b in enumerate(bits)}}

    def get(self,mask):
        if mask not in self.cache:
            last = mask & -mask
            self.cache[mask] = self.e.op(XOR,self.get(mask ^ last),self.cache[last])
        return self.cache[mask]


def parent_word(e,graph,visible,seed=lm.WAVE):
    negative = visible[0]
    invariant = [e.op(XOR,v,negative) for v in visible[1:]]
    pivot = graph.pivot
    rep = invariant[:pivot]+[e.zero]+invariant[pivot:]
    hidden = Parities(e,rep[-20:])
    tab = graph.model.table
    observed = e.majority(*(hidden.get(tab.head(s,0)) for s in (seed,lm.B,lm.D)))
    toggle = e.op(XOR,negative,observed)
    return [e.op(XOR,bit,toggle) if (graph.flip >> i)&1 else bit for i,bit in enumerate(rep)]


def east_bit(e,graph,a,b,threshold):
    def hiddenside(word,d):
        return [word[66+graph.model.table.flag_shift(d)],*word[66+lm.PAYLOAD_SHIFT:]]
    diffs = [[e.op(XOR,x,y) for x,y in zip(report,side,strict=True)] for report,side in
             ((b[52:66],hiddenside(a,-1)),(a[38:52],hiddenside(b,1)))]
    total = Columns(e,3)
    for diff in diffs:
        for block in (diff[:4],diff[4:]):
            terms = [e.op(AND,block[i],block[i+1]) for i in range(0,len(block),2)]
            parity = terms[0]
            for term in terms[1:]:
                parity = e.op(XOR,parity,term)
            total.add(0,parity)
    bits = total.finish()
    # Compare a three-bit number with the fixed integer threshold.
    ge = e.one
    for i,bit in enumerate(bits):
        ge = e.op(AND if (threshold >> i)&1 else OR,bit,ge)
    return ge


def north_bit(e,graph,a,b,threshold):
    model = graph.model
    pools = [Parities(e,s) for s in (b[66:],a[52:66],a[66:],a[38:52])]
    groups = {}
    counts = Counter()
    coefficients = {}
    for child,left,center,right,weight in model.table.terms():
        key = (weight,model.table.used_blocks(left | right))
        if key not in coefficients:
            coefficients[key] = sum(model.perturbation(*key)[:threshold])
        if not coefficients[key]:
            continue
        if key not in groups:
            groups[key] = Columns(e,18)
        counts[key] += 1
        masks = (child,left,center,right)
        chars = [p.get(m) for p,m in zip(pools,masks) if m]
        sign = chars[0]
        for char in chars[1:]:
            sign = e.op(XOR,sign,char)
        if lm.quadratic(left | right):
            sign = e.op(NOT,sign)
        groups[key].add(0,sign)
    assert all(n < 1 << 18 for n in counts.values())
    # index - cumulative multiplicity modulo 2^39. Its high bit detects a borrow.
    width = 39
    offset = -4*model.scale_product*sum(comb(11,i) for i in range(threshold))
    result = Columns(e,width)
    for i,indexbit in enumerate(b[:38]):
        result.add(i,indexbit)
    for key,count in counts.items():
        c = coefficients[key]
        offset -= count*c
        multiplier = 2*c % (1 << width)
        bits = groups[key].finish()[:count.bit_length()]
        for j,bit in enumerate(bits):
            for i in range(width-j):
                if (multiplier >> i)&1:
                    result.add(i+j,bit)
    for i in range(width):
        if (offset >> i)&1:
            result.add(i,e.one)
    return e.op(NOT,result.finish()[-1])


def compile_bond(graph,direction,threshold,patterns=(),wanted=None,consumer=None):
    maximum = {"east":4,"north":11}[direction]
    if not 1 <= threshold <= maximum or wanted is not None and not 0 <= wanted < PADDED:
        raise ValueError("threshold or gate outside its range")
    try:
        e = Emitter(graph.gates,patterns,wanted,consumer)
        # Read every adjacent-product input once in the ideal prefix.
        inputs = [Wire(e.emit(COPY,x.end,x.end),x.value) for x in e.inputs]
        visible = [e.zero]
        for x in inputs:
            visible.append(e.op(XOR,visible[-1],x))
        a,b = parent_word(e,graph,visible[:graph.p]),parent_word(e,graph,visible[graph.p:])
        output = (east_bit if direction == "east" else north_bit)(e,graph,a,b,threshold)
        raw = e.count
        assert raw < PADDED and output.end == raw-1
        if consumer is not None:
            if raw-1 <= consumer < PADDED-1:
                e.found_consumers.append(consumer+1)
            return tuple(e.found_consumers)
        # First pad gate reads the actual output. Subsequent gates copy its predecessor.
        if wanted is not None:
            source = output.end if wanted == raw else wanted-1
            return COPY,source,source
        stats = dict(e.stats)
        stats[COPY] += PADDED-raw
        return raw,stats,output.value
    except GateFound as found:
        return found.gate

