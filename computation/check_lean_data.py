#!/usr/bin/env python3
"""Compare the canonical JSON trees with the concrete generated Lean trees.

This is a data correspondence check, not a Lean parser or proof checker. It
accepts the small generated syntax used in Certificates/Data, expands chunks,
and rejects unrecognized Tree expressions. Compile Lean to check the proofs.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import verify


def without_comments(source):
    """Discard Lean comments while preserving lines and quoted text."""
    output = []
    index = depth = 0
    quoted = False
    while index < len(source):
        if depth:
            if source.startswith("/-", index):
                depth += 1
                output.extend("  ")
                index += 2
            elif source.startswith("-/", index):
                depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if source[index] == "\n" else " ")
                index += 1
        elif quoted:
            char = source[index]
            output.append(char)
            index += 1
            if char == "\\" and index < len(source):
                output.append(source[index])
                index += 1
            elif char == '"':
                quoted = False
        elif source.startswith("/-", index):
            depth = 1
            output.extend("  ")
            index += 2
        elif source.startswith("--", index):
            end = source.find("\n", index)
            if end < 0:
                end = len(source)
            output.extend(" " * (end - index))
            index = end
        else:
            char = source[index]
            output.append(char)
            index += 1
            quoted = char == '"'
    verify.require(depth == 0 and not quoted, "Unterminated Lean comment/string")
    return "".join(output)


def compare(data, lean_dir):
    verify.replay(data)
    lean_dir = Path(lean_dir).resolve()
    cache, active, files = {}, set(), {}

    def rational(source):
        source = source.strip()
        verify.require(re.fullmatch(r"-?\d+(?:\s*/\s*\d+)?", source) is not None,
                       "Unrecognized generated rational")
        value = Fraction(source.replace(" ", ""))
        return f"{value.numerator}/{value.denominator}"

    def read_tree(path):
        if path in cache:
            return cache[path]
        verify.require(path not in active, "Cyclic Lean chunk dependency")
        active.add(path)
        raw = path.read_bytes()
        files[str(path.relative_to(lean_dir))] = hashlib.sha256(raw).hexdigest()
        source = without_comments(raw.decode("utf-8"))
        matches = re.findall(r"def parameters\s*:\s*Parameters\s*:=\s*⟨(\d+),\s*(\d+),\s*(\d+)⟩", source)
        verify.require(len(matches) == 1, "Missing or ambiguous Lean parameters")
        parameters = tuple(map(int, matches[0]))
        pairs = re.findall(r"^private def (node_\d+)\s*:\s*Tree\s*:=\s*(.+)$", source, re.M)
        nodes = {name: definition.strip() for name, definition in pairs}
        verify.require(len(nodes) == len(pairs), "Duplicate generated node")
        roots = re.findall(r"^def tree\s*:\s*Tree\s*:=\s*(node_\d+)\s*$", source, re.M)
        verify.require(len(roots) == 1, "Missing or ambiguous Lean root")

        def expand(name, ancestors=frozenset()):
            verify.require(name not in ancestors, "Cyclic Lean node reference")
            verify.require(name in nodes, "Unknown Lean node reference")
            ancestors = ancestors | {name}
            definition = nodes[name]
            if definition == ".leaf .projection":
                return {"kind": "projection"}
            match = re.fullmatch(r"\.leaf \(\.strip \(([^:]+): ℚ\)\)", definition)
            if match:
                return {"kind": "strip", "T": rational(match.group(1))}
            match = re.fullmatch(r"\.split([CD]) \(([^:]+): ℚ\) (node_\d+) (node_\d+)", definition)
            if match:
                return {"kind": "split", "axis": match.group(1).lower(),
                        "midpoint": rational(match.group(2)),
                        "left": expand(match.group(3), ancestors),
                        "right": expand(match.group(4), ancestors)}
            match = re.fullmatch(r"(C\d+)\.tree", definition)
            verify.require(match is not None, f"Unrecognized generated Tree expression: {definition}")
            chunk_parameters, chunk_tree = read_tree(path.with_suffix("") / (match.group(1) + ".lean"))
            verify.require(chunk_parameters == parameters, "Lean chunk parameter mismatch")
            return chunk_tree

        result = parameters, expand(roots[0])
        active.remove(path)
        cache[path] = result
        return result

    for case in data["cases"]:
        q, m, ell = (case[key] for key in ("q", "m", "l"))
        path = lean_dir / f"CubeSections/Certificates/Data/Q{q}M{m}L{ell}.lean"
        parameters, tree = read_tree(path)
        verify.require(parameters == (q, m, ell), "Lean top-level parameter mismatch")
        verify.require(tree == case["tree"], f"Lean/JSON tree mismatch for {(q, m, ell)}")
    return {"status": "PASS_LEAN_JSON_DATA_CORRESPONDENCE", "cases": len(data["cases"]),
            "lean_data_files": len(files), "lean_source_sha256": dict(sorted(files.items())),
            "scope": "Generated tree data only; Lean compilation is required for proof checking."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-dir", type=Path, default=HERE.parent / "lean")
    parser.add_argument("--certificate", type=Path, default=HERE / "data/pair_trees.json")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = compare(verify.load_json(args.certificate), args.lean_dir)
    report["certificate_sha256"] = verify.sha256(args.certificate)
    output = json.dumps(report, indent=2) + "\n"
    if args.report:
        verify.require(args.report.resolve() != args.certificate.resolve(), "Report would overwrite certificate")
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(output, encoding="utf-8")
    print(output, end="")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, RecursionError, ZeroDivisionError) as error:
        print(f"DATA COMPARISON FAILED: {error}", file=sys.stderr)
        raise SystemExit(1)
