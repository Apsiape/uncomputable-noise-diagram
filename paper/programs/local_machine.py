"""Finite Walsh scattering lists for both observables of one square-lattice magnet."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from collections import deque
from itertools import product
from counter_program import PROGRAM, REGISTERS, WIDTH, LABELS

EMPTY, BIT, GAIN, HEAT, RIGHT, HOME, LEFT = 0, 1, 2, 3, 4, 5, 8
# HOME..HOME+2 and LEFT..LEFT+2 remember ticks mod 3 since the dual seed.
MEMORIES = range(11)
WAVE, MASS, B, D = ("wave",), ("mass",), ("terminal",), ("base",)
RES_BITS, PAYLOAD_SHIFT, LOW_BITS = 4, 7, 4
RESIDENT_DIVISOR, WALKER_DIVISOR = 16, 512
# (signed quarters, power of u, power of z, extra power of 1+z in denominator)
WORK, PASSIVE, BASE = (1, 5, 1, 1), (4, 1, 0, 0), (8, 5, 0, 1)
ORBIT = tuple(("orbit", d, g, t) for d, g, t in product((-1, 1), (False, True), (False, True)))


def plain(memory):
    if HOME <= memory < HOME + 3:
        return HOME
    if LEFT <= memory < LEFT + 3:
        return LEFT
    return memory


def next_memory(old, written):
    if written in (HOME, LEFT):
        phase = (old - plain(old) + 1) % 3
        return written + phase
    return written


def quadratic(bits):
    """Sum of products of adjacent bit pairs, modulo two."""
    parity = 0
    while bits:
        parity ^= int(bits & 3 == 3)
        bits >>= 2
    return parity


def divisor(weight):
    _, power, _, extra = weight
    if not extra:
        return RESIDENT_DIVISOR
    return WALKER_DIVISOR * RESIDENT_DIVISOR**(power-1)


def travel(distance, target, memory):
    direction = 1 if distance > 0 else -1
    rest = distance - direction
    state = ("travel", rest, target) if rest else target
    return state, direction, memory, WORK


def control(state, memory):
    """One ordinary head transition, before decorating the origin with its phase."""
    op, *args = state
    if state in (WAVE, MASS):
        if memory == EMPTY:
            yield ("pc", LABELS[op]), 0, HOME, WORK
    elif state == D:
        if memory == EMPTY:
            yield D, 0, EMPTY, BASE
    elif op == "pc":
        if memory != HOME:
            return
        ins, *par = PROGRAM[args[0]]
        if ins in ("jump", "fork"):
            for address in par:
                yield ("pc", address), 0, HOME, WORK
        elif ins in ("inc", "dec"):
            yield travel(par[0] + 1, (ins, *par), HOME)
        elif ins == "install":
            yield ("install", 0, 0, 0), 1, LEFT, WORK
    elif op == "travel":
        yield travel(*args, memory)
    elif op == "home":
        if memory == HOME:
            yield ("pc", args[0]), 0, HOME, WORK
        else:
            yield state, -1, memory, WORK
    elif op == "inc":
        _, address = args
        if memory == BIT:
            yield travel(WIDTH, state, BIT)
        elif memory == EMPTY:
            yield ("home", address), -1, BIT, WORK
    elif op == "dec":
        reg, nonzero, zero = args
        if memory == EMPTY:
            yield ("home", zero), -1, EMPTY, WORK
        elif memory == BIT:
            yield travel(WIDTH, ("scan", reg, nonzero), BIT)
    elif op == "scan":
        _, address = args
        if memory == BIT:
            yield travel(WIDTH, state, BIT)
        elif memory == EMPTY:
            yield travel(-WIDTH, ("clear", address), EMPTY)
    elif op == "clear":
        if memory == BIT:
            yield ("home", args[0]), -1, EMPTY, WORK
    elif op == "install":
        if memory not in (EMPTY, BIT):
            return
        slot, placed, occupied = args
        flags = {"cut": 1, "heat": 2, "length": 4}
        if memory == BIT:
            occupied |= flags.get(REGISTERS[slot], 0)
        if slot + 1 < WIDTH:
            yield ("install", slot + 1, placed, occupied), 1, EMPTY, WORK
        elif not (occupied & 4):
            yield ("seek_left",), -1, RIGHT, WORK
        else:
            new = (~(placed | occupied)) & 3
            if new == 3:  # The supplied program has strictly distinct interior cuts.
                return
            written = {0: EMPTY, 1: GAIN, 2: HEAT}[new]
            yield ("install", 0, placed | new, 0), 1, written, WORK
    elif op == "seek_left":
        if memory == LEFT:
            yield ("orbit", -1, False, False), 0, LEFT, WORK
        else:
            yield state, -1, memory, WORK
    elif op == "orbit":
        if memory not in (EMPTY, LEFT, GAIN, HEAT, RIGHT):
            return
        direction, gain, thermal = args
        power = 1 + int(memory != EMPTY)
        if memory == LEFT:
            yield ("erase_right",), 1, LEFT, WORK
            direction, gain, thermal = 1, False, False
        elif memory == RIGHT:
            direction, gain, thermal = -1, True, True
        elif memory == GAIN:
            gain = direction == 1
        elif memory == HEAT:
            thermal = direction == 1
        # Holding still does not cross an edge or collect its bonus.
        yield state, 0, memory, (4, power, 0, 1)
        yield ("orbit", direction, gain, thermal), direction, memory, (8 if gain else 4, power, int(thermal), 1)
    elif op == "erase_right":
        if memory == RIGHT:
            yield ("erase_left",), -1, EMPTY, WORK
        else:
            yield state, 1, EMPTY, WORK
    elif op == "erase_left":
        if memory == LEFT:
            yield B, 0, EMPTY, WORK
        else:
            yield state, -1, EMPTY, WORK
    # Terminal B, dead instructions and unlisted cases have empty lists.


def actions(state, memory):
    for target, move, written, weight in control(state, plain(memory)):
        if target == B:
            phase = (memory - LEFT + 1) % 3
            weight = (2 if phase == 0 else -1, *WORK[1:])
        yield target, move, next_memory(memory, written), weight


class Table:
    def __init__(self):
        states = [*ORBIT, B, D, WAVE, MASS]
        seen = set(states)
        pending = deque(states)
        while pending:
            state = pending.popleft()
            for memory in (EMPTY, BIT, GAIN, HEAT, RIGHT, HOME, LEFT):
                for target, _, _, _ in control(state, memory):
                    if target not in seen:
                        seen.add(target)
                        states.append(target)
                        pending.append(target)
        self.states = tuple(states)
        # 11 and 13 are the unused majority triple masks.
        ids = [*range(11), 12, *range(14, len(states) + 2)]
        self.ids = dict(zip(states, ids, strict=True))
        self.payload_bits = max(ids).bit_length()
        self.width = self.payload_bits + 1
        self.lane_size = 1 << self.width
        self.group_size = 1 << (PAYLOAD_SHIFT + self.payload_bits)
        self.blocks = (1 << LOW_BITS, self.lane_size >> LOW_BITS)
        self.scale_product = RESIDENT_DIVISOR**4 * WALKER_DIVISOR
        self.indices = (1 << 13) * self.scale_product
        self.alphabet = self.group_size * self.lane_size**2 * self.indices

    @staticmethod
    def flag_shift(direction):
        return RES_BITS + direction + 1

    def lane(self, y, direction):
        return ((y >> PAYLOAD_SHIFT) << 1) | ((y >> self.flag_shift(direction)) & 1)

    def head(self, state, direction):
        return (self.ids[state] << PAYLOAD_SHIFT) | (1 << self.flag_shift(direction))

    def used_blocks(self, mask):
        low, high = self.blocks
        return ((low,) if mask & (low-1) else ()) + ((high,) if mask >> LOW_BITS else ())

    def spin(self, y, seed=WAVE):
        negatives = sum((y & self.head(s, 0)).bit_count() % 2 for s in (seed, B, D))
        return 1 if negatives <= 1 else -1

    def terms(self):
        """Yield (input mask, left report mask, center mask, right report mask, weight)."""
        for raw in MEMORIES:
            if raw:
                yield raw, 0, next_memory(raw, plain(raw)), 0, PASSIVE
        for state in self.states:
            incoming = (0,) if state in (WAVE, MASS, B, D) else (-1, 0, 1)
            for raw in MEMORIES:
                for target, move, written, weight in actions(state, raw):
                    mask = 1 | (self.ids[target] << 1)
                    left = mask if move == -1 else 0
                    right = mask if move == 1 else 0
                    center = written | (self.head(target, 0) if move == 0 else 0)
                    for direction in incoming:
                        yield raw | self.head(state, direction), left, center, right, weight

