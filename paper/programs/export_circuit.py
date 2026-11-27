"""Export the two objects being compared and untrusted proof hints; no decisions here."""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import json
from pathlib import Path
import herald_circuit as circuit
import small_ising as arithmetic
from bond_circuit import Columns
from binary_wave import BinaryWave


def main():
    root = Path(HERE)
    # Snapshots taken using the public printer before installing any tracing hooks.
    gates = [circuit.gate(i) for i in range(circuit.gate_count())]
    (root / "herald-gates.json").write_bytes(json.dumps(gates, separators=(",", ":")).encode() + b"\n")
    with (root / "binary-terms.tsv").open("w", newline="\n", encoding="ascii") as stream:
        for term in BinaryWave().terms():
            print(*term, sep="\t", file=stream)

    trace = {"words": [], "columns": [], "pops": []}
    raw_emitter = circuit.Raw
    original_decode = circuit.decode_word
    original_east = circuit.horizontal
    original_north = circuit.vertical
    original_pop = arithmetic.population
    original_add = Columns.add
    original_finish = Columns.finish
    annotations = {}

    class RecordingRaw(raw_emitter):
        def __init__(self, width):
            super().__init__(width)
            trace["raw"] = self.ops

    def decode(*args):
        outputs = original_decode(*args)
        trace["words"].append([w.end for w in outputs])
        return outputs

    def horizontal(*args):
        output = original_east(*args)
        trace["east"] = output.end
        return output

    def vertical(*args):
        output = original_north(*args)
        trace["north"] = output.end
        return output

    def population(e, items):
        digits = original_pop(e, items)
        trace["pops"].append([[w.end for w in items], [w.end for w in digits]])
        return digits

    def record(col):
        if col not in annotations:
            entry = {"inputs": [], "spans": []}
            annotations[col] = entry
            trace["columns"].append(entry)
        return annotations[col]

    def add(col, pos, wire):
        entry = record(col)
        entry["inputs"].append([pos, wire.end])
        start = len(col.e.ops)
        original_add(col, pos, wire)
        if start != len(col.e.ops):
            entry["spans"].append([start, len(col.e.ops)])

    def finish(col):
        entry = record(col)
        start = len(col.e.ops)
        outputs = original_finish(col)
        entry["spans"].append([start, len(col.e.ops)])
        entry["digits"] = [w.end for w in outputs]
        return outputs

    circuit.Raw = RecordingRaw
    circuit.decode_word = decode
    circuit.horizontal = horizontal
    circuit.vertical = vertical
    arithmetic.population = population
    Columns.add = add
    Columns.finish = finish
    circuit.network.cache_clear()
    regenerated, _ = circuit.network()
    if regenerated != gates:
        raise ValueError("traced printer changed the emitted circuit")
    trace["groups"] = circuit.encoding().profiles()
    (root / "circuit-hints.json").write_bytes(json.dumps(trace, separators=(",", ":")).encode() + b"\n")
    print(f"{len(gates)} final gates, {len(trace['raw'])} raw gates, {len(trace['columns'])} arithmetic blocks")


if __name__ == "__main__":
    main()
