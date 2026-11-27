"""Universal circuit verifier with an independently assembled Walsh reference."""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from collections import Counter, defaultdict
from functools import cache, reduce
from hashlib import sha256
from itertools import product
import json
from operator import xor
from reference_scattering import reference_terms
from pathlib import Path

ROOT = Path(HERE)
INPUTS = 323
WORD = 105
D = 1 << 56
MOD = 1 << 58
R, L, Y = 57, 71, 85
NORTH = 2 * WORD
ONE = frozenset({0})
ZERO = frozenset()


def require(ok, explanation):
    if not ok:
        raise ValueError(explanation)


def normal_root(ops, table):
    """Hash-cons by exact tuple equality; low bit denotes Boolean negation."""
    refs = {-(i + 1): 2 * (i + 1) for i in range(INPUTS)}
    for n, (op, a, b) in enumerate(ops):
        require(op in (0, 3, 6, 8, 12, 14, 15) and a in refs and b in refs, ("bad source", n))
        x, y = sorted((refs[a], refs[b]))
        if op in (0, 15):
            value = int(op == 15)
        elif op in (3, 12):
            value = refs[a] ^ int(op == 3)
        elif x == y:
            value = 0 if op == 6 else x
        elif x < 2:
            if op == 6:
                value = x ^ y
            elif op == 8:
                value = y if x else 0
            else:
                value = 1 if x else y
        else:
            key = (op, x, y)
            if key not in table:
                table[key] = 2 * (INPUTS + len(table) + 1)
            value = table[key]
        refs[n] = value
    return refs[len(ops) - 1]


def boolean_product(a, b):
    result = set()
    for u in a:
        for v in b:
            monomial = u | v
            result.symmetric_difference_update((monomial,))
    return frozenset(result)


def expression(raw, cuts):
    """Boolean algebraic normal form over independent variables at a cut."""
    @cache
    def read(i):
        if i in cuts:
            return cuts[i]
        require(0 <= i < len(raw), ("unaccounted input", i))
        op, a, b = raw[i]
        if op in (0, 15):
            return ONE if op else ZERO
        u = read(a)
        if op == 12:
            return u
        if op == 3:
            return ONE ^ u
        v = read(b)
        if op == 6:
            return u ^ v
        uv = boolean_product(u, v)
        return uv if op == 8 else uv ^ u ^ v
    return read


def variable(i):
    return frozenset({1 << i})


def verify_decoders(raw, words):
    require(len(words) == 3 and all(len(w) == WORD for w in words), "word widths")
    read = expression(raw, {-1-i: variable(i) for i in range(INPUTS)})
    flips = {R, L, Y+4, Y+5, Y+6}
    for k, word in enumerate(words):
        base = k * WORD
        rep = [ZERO if i == R else variable(base+1+i-int(i > R)) for i in range(WORD)]
        parities = []
        for label in (12, 8, 9):  # mass, terminal, direct, in the published alphabet
            mask = 32 | (label << 7)
            parities.append(reduce(xor, (rep[Y+j] for j in range(20) if mask >> j & 1), ZERO))
        a, b, c = parities
        toggle = variable(base) ^ boolean_product(a, b) ^ boolean_product(a, c) ^ boolean_product(b, c)
        for j, wire in enumerate(word):
            require(read(wire) == (rep[j] ^ toggle if j in flips else rep[j]), ("decoder", k, j))
    require(len(set(sum(words, []))) == 3 * WORD, "ambiguous word cut")


def verify_east(read, gate):
    west_lane = [Y+4, *range(Y+7, Y+20)]
    east_lane = [WORD+Y+6, *range(WORD+Y+7, WORD+Y+20)]
    differences = [variable(i) ^ variable(j) for i, j in zip(
        [*range(WORD+L, WORD+L+14), *range(R, R+14)], west_lane+east_lane, strict=True)]
    q = reduce(xor, (boolean_product(differences[i], differences[i+1]) for i in range(0,28,2)), ZERO)
    require(read(gate) == q, "east quadratic")


def truth(op, a, b):
    return op >> (2*a+b) & 1


def compressors(raw, spans, statistics):
    for start, end in spans:
        k = start
        while k < end:
            op, a, b = raw[k]
            require(op == 6 and k+1 < end and raw[k+1] == [8,a,b], ("compressor", k))
            full = k+4 < end and raw[k+2][:2] == [6,k]
            if full:
                c = raw[k+2][2]
                args, outputs, size = (a,b,c), (k+2,k+4), 5
            else:
                args, outputs, size = (a,b), (k,k+1), 2
            for values in product(range(2), repeat=len(set(args))):
                context = dict(zip(dict.fromkeys(args), values))
                for j in range(k, k+size):
                    f, l, r = raw[j]
                    context[j] = truth(f, context[l], context[r])
                require(sum(context[i] for i in args) == context[outputs[0]]+2*context[outputs[1]],
                        ("failed local arithmetic identity", k))
            yield args, outputs
            statistics[len(args)] += 1
            k += size
        require(k == end, "compressor span overrun")


def verify_columns(raw, entry, statistics):
    digits = entry["digits"]
    modulus = 1 << len(digits)
    weights = Counter()
    for j, bit in enumerate(digits):
        weights[bit] += 1 << j
    blocks = list(compressors(raw, entry["spans"], statistics))
    for sources, (low, high) in reversed(blocks):
        w = weights.pop(low, 0)
        carry = weights.pop(high, 0)
        require((carry-2*w) % modulus == 0, ("unbalanced carry", low, high))
        for source in sources:
            weights[source] += w
    for shift, wire in entry["inputs"]:
        weights[wire] -= 1 << shift
    # Raw gate zero is an independently checked literal zero.
    require(raw[0][0] == 0, "raw zero")
    require(all(wire == 0 or value % modulus == 0 for wire,value in weights.items()), "column identity")


def parent_data():
    """Literal expansion of the model definition D + sum c chi, no evaluator or profile code."""
    terms = Counter()
    norm = count = 0
    for child, left, center, right, coefficient in reference_terms():
        require(0 <= child < 1<<20 and 0 <= center < 1<<20 and
                0 <= left < 1<<14 and 0 <= right < 1<<14, "mask widths")
        mask = (child << (NORTH+Y)) | (left << L) | (center << Y) | (right << R)
        terms[mask] += coefficient
        norm += abs(coefficient)
        count += 1
    require((count, norm) == (164852, 33293550733133931) and norm < D, "table size or norm")
    return terms


def lift_mask(mask, positions):
    require(0 <= mask < 1 << len(positions), "out-of-range factor mask")
    return sum(1 << p for j,p in enumerate(positions) if mask >> j & 1)


def signatures(read, inputs):
    out = []
    for wire in inputs:
        terms = read(wire)
        require(all(m.bit_count() < 2 for m in terms), ("noncharacter", wire))
        out.append((sum(m for m in terms if m), -1 if 0 in terms else 1))
    return tuple(sorted(out))


def add_scaled(total, other, factor):
    for key, value in other.items():
        total[key] += factor*value


def multiply(p, q):
    result = Counter()
    for a, c in p.items():
        for b, d in q.items():
            result[a | b] += c*d
    return result


def bind(cuts, wire, poly):
    require(wire not in cuts or cuts[wire] == poly, ("inconsistent arithmetic cut", wire))
    cuts[wire] = poly


def verify_north(raw, t, read, reference):
    statistics = Counter()
    columns = {}
    for entry in t["columns"]:
        verify_columns(raw, entry, statistics)
        key = tuple(entry["digits"])
        require(key not in columns, "reused column output")
        columns[key] = entry
    zero = Counter()
    unit = Counter({0: 1})
    cuts = {0: zero, 1: unit}
    require(raw[1][0] == 15, "raw one")
    counts = {}
    next_id = 57
    for ins, digits in t["pops"]:
        width = len(ins).bit_length()
        require(len(digits) == width and ins, "popcount width")
        if len(ins) == 1:
            require(digits == ins, "singleton popcount")
        else:
            entry = columns.pop(tuple(digits))
            require(Counter(tuple(pair) for pair in entry["inputs"]) == Counter((0,w) for w in ins),
                    "popcount addends")
        sig = signatures(read, ins)
        if sig not in counts:
            pol = Counter({0:len(ins)})
            bases = []
            for j, wire in enumerate(digits):
                # A constant raw wire is an actual constant, including singleton populations.
                base = cuts[wire] if wire in (0,1) else Counter({1 << next_id:1})
                next_id += 1
                bases.append(base)
                add_scaled(pol, base, -(2 << j))
            counts[sig] = bases, pol
        bases, _ = counts[sig]
        for wire, base in zip(digits,bases,strict=True):
            bind(cuts, wire, base)

    require(len(columns) == 1, "missing final accumulator")
    entry = next(iter(columns.values()))
    require(len(entry["digits"]) == 58 and raw[t["north"]] == [3,entry["digits"][-1],entry["digits"][-1]],
            "north sign bit")
    target = Counter({0:-D})
    for j, wire in enumerate(t["words"][2][:57]):
        bit = Counter({1 << j:1})
        bind(cuts, wire, bit)
        add_scaled(target, bit, 1 << j)
    expansion = Counter()
    low_places = [*range(NORTH+Y,NORTH+Y+7),*range(Y,Y+4),Y+5,L,R]
    src_places = list(range(NORTH+Y+7,NORTH+Y+20))
    destinations = {"left":list(range(L+1,L+14)), "right":list(range(R+1,R+14)),
                    "center":list(range(Y+7,Y+20)), "passive":[]}
    for dest, coeff, low, high in t["groups"]:
        low_sig = tuple(sorted((lift_mask(mask,low_places),s) for mask,s in low))
        high_sig = tuple(sorted((lift_mask(inp,src_places) ^ lift_mask(out,destinations[dest]),s)
                                for inp,out,s in high))
        require(all(abs(s) == 1 for _,s in low_sig+high_sig), "invalid sign")
        for u, s in low_sig:
            for v, h in high_sig:
                expansion[u ^ v] += coeff*s*h
        add_scaled(target, multiply(counts[low_sig][1], counts[high_sig][1]), -coeff)
    require(expansion == reference, "Walsh expansion differs from literal table")

    @cache
    def arithmetic(wire):
        if wire in cuts:
            return cuts[wire]
        require(wire >= 0, "unexplained arithmetic input")
        op,a,b = raw[wire]
        if op == 3:
            result = unit.copy()
            add_scaled(result,arithmetic(a),-1)
            return result
        require(op == 8, ("unexplained arithmetic gate", wire, op))
        return multiply(arithmetic(a),arithmetic(b))

    for j, wire in entry["inputs"]:
        add_scaled(target,arithmetic(wire), -(1 << j))
    require(all(c % MOD == 0 for c in target.values()), "integer product or signed accumulator mismatch")
    return {"columns":len(t["columns"]), "popcounts":len(t["pops"]), "half_adders":statistics[2],
            "full_adders":statistics[3], "profiles":len(t["groups"]), "walsh_masks":len(reference)}


def verify_slots(t):
    raw = t["raw"]
    for e,n in product(range(2), repeat=2):
        for slot,cal in product(range(128),range(2)):
            cuts = {t["east"]:e, t["north"]:n, -323:cal}
            cuts.update({-316-i:(slot >> i)&1 for i in range(7)})
            def value(w):
                if w not in cuts:
                    require(w >= 0, "other input to output table")
                    op,a,b = raw[w]
                    if op in (0,15):
                        cuts[w] = op//15
                    else:
                        left = value(a)
                        right = left if op in (3,12) else value(b)
                        cuts[w] = truth(op,left,right)
                return cuts[w]
            expected = (slot >= 64 if e+n == 0 else slot >= 40 if e+n == 1 else cal if slot < 18 else slot >= 25)
            require(value(len(raw)-1) == expected, ("slot table",e,n,slot,cal))


def main():
    gate_file = ROOT/"herald-gates.json"
    gates = json.loads(gate_file.read_bytes())
    t = json.loads((ROOT/"circuit-hints.json").read_bytes())
    raw = t["raw"]
    table = {}
    require(len(gates) == 85041 and normal_root(gates, table) == normal_root(raw, table), "printed root mismatch")
    words = t["words"]
    verify_decoders(raw, words)
    read = expression(raw, {w:variable(j) for j,w in enumerate(sum(words,[]))})
    verify_east(read, t["east"])
    result = verify_north(raw,t,read,parent_data())
    verify_slots(t)
    result.update(verdict="PASS", final_gates=len(gates), raw_gates=len(raw), primary_bits=INPUTS,
                  reference="independently coded 235-instruction assembly, checked equal to the printed table",
                  slot_rows=1024, gate_sha256=sha256(gate_file.read_bytes()).hexdigest(),
                  terms_sha256=sha256((ROOT/"binary-terms.tsv").read_bytes()).hexdigest())
    data = json.dumps(result,indent=2,sort_keys=True)
    (ROOT/"CIRCUIT-CERTIFICATE.json").write_bytes(data.encode()+b"\n")
    print(data)


if __name__ == "__main__":
    main()
