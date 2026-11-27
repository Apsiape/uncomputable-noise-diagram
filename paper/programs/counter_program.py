"""Finite control for the bounded two-counter interpreter of the binary-energy parent."""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

REGISTERS = ("stage", "todo", "code", "num", "den", "cut", "heat", "length",
             "dilute", "fuel", "pc", "x", "y", "list", "skip", "op", "tmp")
WIDTH = len(REGISTERS)


class Builder:
    """Expand arithmetic into increment, conditional decrement and finite jumps."""

    def __init__(self):
        self.ins = []
        self.labels = {}
        self.serial = 0

    def fresh(self):
        self.serial += 1
        return f".{self.serial}"

    def label(self, name):
        assert name not in self.labels
        self.labels[name] = len(self.ins)
        return name

    def emit(self, *instruction):
        self.ins.append(instruction)

    def inc(self, reg):
        self.emit("inc", reg)

    def jump(self, target):
        self.emit("jump", target)

    def dec(self, reg, nonzero, zero):
        self.emit("dec", reg, nonzero, zero)

    def drain(self, source, *destinations):
        """Move units out of source, adding one to each named destination."""
        assert source not in destinations
        loop = self.label(self.fresh())
        body, end = self.fresh(), self.fresh()
        self.dec(source, body, end)
        self.label(body)
        for dest in destinations:
            self.inc(dest)
        self.jump(loop)
        self.label(end)

    def copy(self, source, dest):
        assert source != dest and "tmp" not in (source, dest)
        self.drain(dest)
        self.drain(source, dest, "tmp")
        self.drain("tmp", source)

    def quadruple(self, reg):
        self.drain(reg, "tmp", "tmp", "tmp", "tmp")
        self.drain("tmp", reg)

    def half(self, reg, even, odd):
        """Replace reg by floor(reg/2) and branch on its original parity."""
        loop = self.label(self.fresh())
        one, two, end0, end1 = [self.fresh() for _ in range(4)]
        self.dec(reg, one, end0)
        self.label(one)
        self.dec(reg, two, end1)
        self.label(two)
        self.inc("tmp")
        self.jump(loop)
        for here, dest in ((end0, even), (end1, odd)):
            self.label(here)
            self.drain("tmp", reg)
            self.jump(dest)

    def finish(self):
        binary = []
        for pc, (op, *args) in enumerate(self.ins):
            if op == "inc":
                binary.append((op, REGISTERS.index(args[0]), pc + 1))
            elif op == "dec":
                reg, nz, z = args
                binary.append((op, REGISTERS.index(reg), self.labels[nz], self.labels[z]))
            else:
                binary.append((op, *(self.labels[arg] for arg in args)))
        return tuple(binary)


def build_program():
    b = Builder()
    b.label("wave")
    b.inc("dilute")
    b.label("mass")
    b.label("choose")
    b.emit("fork", "later", "begin")
    b.label("later")
    b.inc("stage")
    b.jump("choose")

    b.label("begin")
    for _ in range(2):
        b.inc("num")
    for _ in range(4):
        b.inc("den")
    b.copy("stage", "todo")
    b.label("next_code")
    b.dec("todo", "simulate", "finish")

    b.label("simulate")
    b.quadruple("num")
    b.quadruple("den")
    b.copy("stage", "fuel")
    for reg in ("pc", "x", "y"):
        b.drain(reg)

    b.label("step")
    b.copy("code", "list")
    b.copy("pc", "skip")
    b.label("fetch")
    b.dec("list", "nonempty", "halted")
    b.label("nonempty")
    b.inc("list")
    b.drain("op")
    # Each cons cell is 2**op * (2*tail+1). Halving the final odd word yields tail.
    b.label("peel")
    b.half("list", "one_factor", "popped")
    b.label("one_factor")
    b.inc("op")
    b.jump("peel")
    b.label("popped")
    b.dec("skip", "fetch", "have_op")
    b.label("have_op")
    b.dec("fuel", "execute", "end_code")
    b.label("execute")
    b.half("op", "low0", "low1")
    b.label("low0")
    b.half("op", "inc_x", "dec_x")
    b.label("low1")
    b.half("op", "inc_y", "dec_y")

    for reg in ("x", "y"):
        b.label("inc_" + reg)
        b.inc(reg)
        b.jump("advance")
        b.label("dec_" + reg)
        b.dec(reg, "take_jump", "advance")
    b.label("advance")
    b.inc("pc")
    b.jump("step")
    b.label("take_jump")
    b.drain("pc")
    b.drain("op", "pc")
    b.jump("step")
    b.label("halted")
    b.inc("num")
    b.label("end_code")
    b.inc("code")
    b.jump("next_code")

    b.label("finish")
    # Orbit length in blocks is (stage+2)*den for wave, 2*den for mass.
    b.copy("den", "length")
    b.copy("den", "heat")
    b.drain("heat", "length")
    b.dec("dilute", "extra", "make_cuts")
    b.label("extra")
    b.dec("stage", "add_length", "make_cuts")
    b.label("add_length")
    b.copy("den", "heat")
    b.drain("heat", "length")
    b.jump("extra")
    b.label("make_cuts")
    b.copy("length", "cut")
    b.copy("length", "heat")
    b.label("subtract")
    b.dec("num", "minus_one", "subtract_heat")
    b.label("minus_one")
    b.dec("cut", "subtract", "invalid")
    b.label("subtract_heat")
    b.dec("den", "minus_heat", "shorten")
    b.label("minus_heat")
    b.dec("heat", "subtract_heat", "invalid")
    b.label("shorten")
    b.dec("cut", "cut_short", "invalid")
    b.label("cut_short")
    b.dec("heat", "heat_short", "invalid")
    b.label("heat_short")
    b.dec("length", "den_short", "invalid")
    b.label("den_short")
    for reg in REGISTERS:
        if reg not in ("cut", "heat", "length"):
            b.drain(reg)
    b.emit("install")
    b.label("invalid")
    b.emit("dead")
    return b.finish(), dict(b.labels)


PROGRAM, LABELS = build_program()

