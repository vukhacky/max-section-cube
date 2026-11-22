#!/usr/bin/env python3
"""Regenerate the canonical pair trees from the deterministic manuscript recursion.

The generator uses exact rational arithmetic. Its output is independently replayed
by verify.py before comparison or writing. It never overwrites tracked data by default.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import verify

SURPLUS = F(1, 4000)
BISECTIONS = 10
DEPTH_LIMIT = 30


def rational(value):
    return f"{value.numerator}/{value.denominator}"


def envelope(q, multiplicity, low, high):
    a, z = F(1, q + 1), 1 - q * low
    curvature = a / 2 * (1 + (a + z) / 3 + (a * a + a * z + z * z) / (6 * (1 - a)))
    quotient = F(1) if multiplicity == q else (1 - q * low) / (1 - multiplicity * low)
    return curvature / 2 * quotient * (q + 1 - 1 / high)


def generate_case(q, m, ell):
    if (q, m, ell) not in verify.EXPECTED_CASES:
        raise ValueError("Invalid multiplicity type")
    a, b = F(1, q + 1), F(1, q)
    exponent = 2 * q - m - ell
    R = b * (1 + b)**(exponent // 2) * (1 + b / 2)**(exponent % 2)
    counts = Counter()
    maximum_depth = 0

    def recurse(x, upper_x, y, upper_y, depth):
        nonlocal maximum_depth
        S = envelope(q, m, x, upper_x) + envelope(q, ell, y, upper_y) + SURPLUS
        K = F(2, 9) + (2 - m * x - ell * y) / 4

        def angular_test(v):
            return 3 * v * v > 5 * (S * K * (15 + v))**2

        lower_v = max(F(0), 1 - (1 - m * x) * (1 - ell * y) / (m * ell * x * y))
        if angular_test(lower_v):
            counts["projection"] += 1
            maximum_depth = max(maximum_depth, depth)
            return {"kind": "projection"}
        lower, upper = F(0), F(1)
        if angular_test(F(1)):
            for _ in range(BISECTIONS):
                middle = (lower + upper) / 2
                sine = 2 * middle / (1 + middle * middle)
                if angular_test(sine * sine):
                    upper = middle
                else:
                    lower = middle
        T = upper
        U = 2 * T / (1 + T * T)
        cosine = (1 - T * T) / (1 + T * T)
        gram = min(x, y)
        L = (x + y) / 2 + gram * cosine - upper_x * upper_y * U * U
        eta = L * gram / (2 * R)
        # Check the analytic sign hypotheses before testing the squared expression.
        if L <= 0 or not 0 <= eta <= F(1, 2):
            raise ArithmeticError("Strip sign or monotonicity guard failed")
        if L * L > 2 * R * T * (1 + upper_x * upper_y * U * U / 4) * (1 - eta * U)**2:
            counts["strip"] += 1
            maximum_depth = max(maximum_depth, depth)
            return {"kind": "strip", "T": rational(T)}
        if depth >= DEPTH_LIMIT:
            raise ArithmeticError(f"Unresolved rectangle at depth {depth} for {(q, m, ell)}")
        if upper_x - x >= upper_y - y:
            middle = (x + upper_x) / 2
            return {"kind": "split", "axis": "c", "midpoint": rational(middle),
                    "left": recurse(x, middle, y, upper_y, depth + 1),
                    "right": recurse(middle, upper_x, y, upper_y, depth + 1)}
        middle = (y + upper_y) / 2
        return {"kind": "split", "axis": "d", "midpoint": rational(middle),
                "left": recurse(x, upper_x, y, middle, depth + 1),
                "right": recurse(x, upper_x, middle, upper_y, depth + 1)}

    tree = recurse(a, b, a, b, 0)
    return {"q": q, "m": m, "l": ell,
            "root_box": {"c": [rational(a), rational(b)], "d": [rational(a), rational(b)]},
            "counts": {"projection": counts["projection"], "strip": counts["strip"],
                       "leaves": sum(counts.values()), "maximum_depth": maximum_depth},
            "tree": tree}


def generate():
    cases = [generate_case(q, m, ell) for q in (2, 3, 4)
             for m in range(1, q + 1) for ell in range(m, q + 1)]
    totals = {str(q): {"pairs": sum(case["q"] == q for case in cases),
                      "projection": sum(case["counts"]["projection"] for case in cases if case["q"] == q),
                      "strip": sum(case["counts"]["strip"] for case in cases if case["q"] == q),
                      "maximum_depth": max(case["counts"]["maximum_depth"] for case in cases if case["q"] == q)}
              for q in (2, 3, 4)}
    return {"schema_version": "cube-pair-cover/1",
            "rational_encoding": "canonical numerator/positive_denominator strings",
            "surplus": "1/4000", "gamma_upper": "1/4", "angle_bisections": BISECTIONS,
            "case_count": len(cases), "leaf_count": sum(case["counts"]["leaves"] for case in cases),
            "counts_by_quotient": totals, "cases": cases}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--check", action="store_true", help="Require byte-identical regeneration; do not write data")
    action.add_argument("--output", type=Path, help="Write a newly generated candidate outside canonical data")
    args = parser.parse_args()
    generated = generate()
    report = verify.replay(generated)
    raw = (json.dumps(generated, indent=2) + "\n").encode("utf-8")
    canonical = HERE / "data/pair_trees.json"
    if args.check:
        verify.require(raw == canonical.read_bytes(), "Generated data differ from the canonical certificate")
        report["regeneration"] = "BYTE_IDENTICAL"
    else:
        verify.require(args.output.resolve() != canonical.resolve(), "Write a candidate, review its diff, then update canonical data explicitly")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(raw)
        report["regeneration"] = "CANDIDATE_WRITTEN"
    print(json.dumps({"status": report["regeneration"], "sha256": hashlib.sha256(raw).hexdigest(),
                      "cases": report["cases"], "nodes": report["nodes"], "leaves": report["leaves"]}, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, ArithmeticError, OSError) as error:
        print(f"REGENERATION FAILED: {error}", file=sys.stderr)
        raise SystemExit(1)
