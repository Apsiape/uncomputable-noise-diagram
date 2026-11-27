"""Print either oriented bond of the square-lattice magnet by alphabet ordinal."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from collections import Counter
from functools import lru_cache
from math import comb, isqrt
import argparse
import json

from counter_program import PROGRAM, WIDTH
from local_machine import Table, LOW_BITS, MASS, WAVE, RESIDENT_DIVISOR, WALKER_DIVISOR, divisor, quadratic


def multiply(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return result


def binomial(n, sign=1):
    return [comb(n, k) * sign**k for k in range(n + 1)]


class Magnet:
    def __init__(self, table=None):
        self.table = Table() if table is None else table
        self.b = self.table.lane_size
        self.g = self.table.group_size
        self.scale_product = self.table.scale_product
        self.I = self.table.indices

    def describe(self):
        t = self.table
        return {"lattice": "Z^2", "edges": ["east", "north"],
                "registers": WIDTH, "program_instructions": len(PROGRAM),
                "head_states": len(t.states), "head_lane_size": self.b,
                "hidden_alphabet": self.g, "resident_divisor": RESIDENT_DIVISOR,
                "walker_divisor": WALKER_DIVISOR, "list_length": self.I,
                "physical_alphabet": t.alphabet,
                "physical_alphabet_log2": t.alphabet.bit_length() - 1,
                "report_blocks": t.blocks,
                "horizontal_energy_range": [0, 4], "vertical_energy_range": [0, 11]}

    def unpack(self, ordinal):
        if not 0 <= ordinal < self.table.alphabet:
            raise ValueError("physical symbol outside alphabet")
        quotient, index = divmod(ordinal, self.I)
        quotient, right_report = divmod(quotient, self.b)
        hidden, left_report = divmod(quotient, self.b)
        return hidden, left_report, right_report, index

    def horizontal(self, west, east):
        y, _, right, _ = self.unpack(west)
        v, left, _, _ = self.unpack(east)
        differences = (left ^ self.table.lane(y, -1), right ^ self.table.lane(v, 1))
        return sum(quadratic(x & ((1 << LOW_BITS)-1)) + quadratic(x >> LOW_BITS) for x in differences)

    @lru_cache(maxsize=32)
    def perturbation(self, weight, blocks):
        units, power, zpower, extra_denominator = weight
        assert 2 * power > len(blocks)
        poly = binomial(2 * power - len(blocks), -1)
        for size in blocks:
            root = isqrt(size)
            assert root*root == size
            poly = multiply(poly, [root + 1, root - 1])
        poly = multiply(poly, binomial(11 - 2 * power - extra_denominator))
        scale = units * (self.scale_product // divisor(weight))
        return (0,) * zpower + tuple(scale * coefficient for coefficient in poly)

    @lru_cache(maxsize=16)
    def row(self, left, center, right, child):
        if not (0 <= left < self.b and 0 <= right < self.b and
                0 <= center < self.g and 0 <= child < self.g):
            raise ValueError("row coordinate outside its alphabet")
        signs = Counter()
        for a, lm, cm, rm, weight in self.table.terms():
            parity = (((a & child) ^ (lm & left) ^ (cm & center) ^ (rm & right)).bit_count()
                      + quadratic(lm | rm)) % 2
            signs[weight, self.table.used_blocks(lm | rm)] += 1 - 2 * parity
        counts = [4 * self.scale_product * x for x in binomial(11)]
        for (weight, blocks), signed_count in signs.items():
            for degree, coefficient in enumerate(self.perturbation(weight, blocks)):
                counts[degree] += signed_count * coefficient
        assert min(counts) > 0 and sum(counts) == self.I
        return tuple(counts)

    def vertical(self, south, north):
        y, left, right, _ = self.unpack(south)
        child, _, _, index = self.unpack(north)
        for energy, multiplicity in enumerate(self.row(left, y, right, child)):
            if index < multiplicity:
                return energy
            index -= multiplicity
        raise AssertionError("invalid energy list")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("describe")
    for command in ("horizontal", "vertical"):
        sub = commands.add_parser(command)
        sub.add_argument("earlier", type=int)
        sub.add_argument("later", type=int)
    row = commands.add_parser("row", help="multiplicities for vertical energies 0 through 11")
    for coordinate in ("left", "center", "right", "child"):
        row.add_argument(coordinate, type=int)
    spin = commands.add_parser("spin")
    spin.add_argument("symbol", type=int)
    spin.add_argument("--observable", choices=("wave", "mass"), default="wave")
    args = parser.parse_args()
    model = Magnet()
    if args.command == "describe":
        result = model.describe()
    elif args.command == "row":
        result = model.row(args.left, args.center, args.right, args.child)
    elif args.command == "spin":
        result = model.table.spin(model.unpack(args.symbol)[0], WAVE if args.observable == "wave" else MASS)
    else:
        result = getattr(model, args.command)(args.earlier, args.later)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

