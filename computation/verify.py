#!/usr/bin/env python3
"""Replay all finite pair certificates with exact rational arithmetic.

The checker recomputes every leaf inequality and the complete closed cover.
It does not import the generator or either manuscript verification program.
Its real-variable soundness is proved in the manuscript and the Lean sources.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
EXPECTED_CASES = {(q, m, ell) for q in (2, 3, 4)
                  for m in range(1, q + 1) for ell in range(m, q + 1)}
DATA_KEYS = {"schema_version", "rational_encoding", "surplus", "gamma_upper",
             "angle_bisections", "case_count", "leaf_count", "counts_by_quotient", "cases"}
COUNT_KEYS = {"projection", "strip", "leaves", "maximum_depth"}
PARAMETERS = {"quotients": [2, 3, 4], "multiplicities": "1 <= m <= l <= q",
              "domain": "[1/(q+1),1/q]^2", "surplus": "1/4000", "gamma_upper": "1/4",
              "angle_bisections": 10, "generator_depth_limit": 30}
SCRIPT_NAMES = ["verify_pairs.py", "verify_pairs_independent.py", "verify.py", "regenerate.py",
                "check_lean_data.py", "export_lean.py", "refresh_manifest.py", "tests/test_verifier.py"]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def reject_nonfinite(value):
    raise ValueError(f"Non-JSON numeric constant: {value}")


def load_json(path):
    return json.loads(Path(path).read_text(encoding="utf-8"),
                      object_pairs_hook=unique_object, parse_constant=reject_nonfinite)


def integer(value, name, minimum=0):
    require(type(value) is int and value >= minimum, f"Invalid integer {name}")
    return value


def rational(value):
    require(isinstance(value, str) and re.fullmatch(
        r"-?(?:0|[1-9][0-9]*)/[1-9][0-9]*", value) is not None,
        "Rationals must be numerator/positive_denominator strings")
    numerator, denominator = value.split("/")
    result = F(int(numerator), int(denominator))
    require(value == f"{result.numerator}/{result.denominator}", "Noncanonical rational")
    return result


def charge_upper(q, multiplicity, low, high):
    a, z = F(1, q + 1), 1 - q * low
    # Combined polynomial form of C_q, independent of the generator's formula.
    curvature = a * (6 * (1 - a) + 2 * (1 - a) * (a + z)
                     + a * a + a * z + z * z) / (12 * (1 - a))
    quotient = F(1) if multiplicity == q else (1 - q * low) / (1 - multiplicity * low)
    return curvature * quotient * ((q + 1) * high - 1) / (2 * high)


def count_object(counts):
    require(isinstance(counts, dict) and set(counts) == COUNT_KEYS, "Invalid case counts")
    for key, value in counts.items():
        integer(value, key)


def replay(data):
    """Validate data independently of file hashes; return recomputed statistics."""
    require(isinstance(data, dict) and set(data) == DATA_KEYS, "Unexpected certificate fields")
    require(data["schema_version"] == "cube-pair-cover/1", "Wrong certificate schema")
    require(data["rational_encoding"] == "canonical numerator/positive_denominator strings",
            "Wrong rational encoding declaration")
    require(rational(data["surplus"]) == F(1, 4000), "Wrong surplus")
    require(rational(data["gamma_upper"]) == F(1, 4), "Wrong gamma upper bound")
    require(integer(data["angle_bisections"], "angle_bisections") == 10,
            "Wrong angle-bisection count")
    integer(data["case_count"], "case_count")
    integer(data["leaf_count"], "leaf_count")
    cases = data["cases"]
    require(isinstance(cases, list), "Cases must be a list")
    actual = []
    for case in cases:
        require(isinstance(case, dict) and set(case) ==
                {"q", "m", "l", "root_box", "counts", "tree"}, "Unexpected case fields")
        triple = tuple(integer(case[key], key, 1) for key in ("q", "m", "l"))
        actual.append(triple)
        count_object(case["counts"])
    require(len(actual) == len(EXPECTED_CASES) and set(actual) == EXPECTED_CASES,
            "Missing, duplicated, or unexpected multiplicity case")

    results = []
    for case in cases:
        q, m, ell = (case[key] for key in ("q", "m", "l"))
        a, b = F(1, q + 1), F(1, q)
        roots = case["root_box"]
        require(isinstance(roots, dict) and set(roots) == {"c", "d"}, "Wrong root-box fields")
        for axis in ("c", "d"):
            require(isinstance(roots[axis], list) and len(roots[axis]) == 2, "Wrong root interval")
            require([rational(value) for value in roots[axis]] == [a, b], "Wrong root domain")
        counts = Counter()
        maximum_depth = node_count = 0

        def visit(node, box, depth):
            nonlocal node_count, maximum_depth
            # Resource guard, not an acceptance shortcut: every accepted leaf is replayed.
            require(depth <= 64, "Certificate exceeds supported tree depth")
            node_count += 1
            require(node_count <= 1_000_000, "Certificate exceeds supported node count")
            require(isinstance(node, dict), "Tree node must be an object")
            x, upper_x, y, upper_y = box
            require(a <= x < upper_x <= b and a <= y < upper_y <= b, "Invalid inherited rectangle")
            kind = node.get("kind")
            if kind == "split":
                require(set(node) == {"kind", "axis", "midpoint", "left", "right"},
                        "Split must have exactly two children")
                midpoint = rational(node["midpoint"])
                if node["axis"] == "c":
                    require(midpoint == (x + upper_x) / 2, "Wrong c midpoint")
                    require(upper_x - x >= upper_y - y, "Wrong longest-side c split")
                    left = (x, midpoint, y, upper_y)
                    right = (midpoint, upper_x, y, upper_y)
                else:
                    require(node["axis"] == "d", "Unknown split axis")
                    require(midpoint == (y + upper_y) / 2, "Wrong d midpoint")
                    require(upper_y - y > upper_x - x, "Wrong longest-side d split")
                    left = (x, upper_x, y, midpoint)
                    right = (x, upper_x, midpoint, upper_y)
                visit(node["left"], left, depth + 1)
                visit(node["right"], right, depth + 1)
                return

            require(kind in ("projection", "strip"), "Unknown leaf kind")
            S = charge_upper(q, m, x, upper_x) + charge_upper(q, ell, y, upper_y) + F(1, 4000)
            K = F(2, 9) + (2 - m * x - ell * y) / 4
            require(S > 0 and K > 0, "Nonpositive angular quantities")

            def angular_test(v):
                require(0 <= v <= 1, "Angle test outside its domain")
                return 3 * v**2 > 5 * S**2 * K**2 * (15 + v)**2

            if kind == "projection":
                require(set(node) == {"kind"}, "Unexpected projection fields")
                v = max(F(0), 1 - (1 / (m * x) - 1) * (1 / (ell * y) - 1))
                require(angular_test(v), "Projection inequality failed")
            else:
                require(set(node) == {"kind", "T"}, "Unexpected strip fields")
                T = rational(node["T"])
                require(0 <= T <= 1, "Threshold outside [0,1]")
                U = 2 * T / (1 + T * T)
                require(T == 1 or angular_test(U * U), "Threshold upper-angle certificate failed")
                gram = min(x, y)
                L = (x + y) / 2 + gram * (1 - T * T) / (1 + T * T) - upper_x * upper_y * U * U
                exponent = 2 * q - m - ell
                R = F(1, q) * (1 + F(1, q))**(exponent // 2) * (1 + F(1, 2 * q))**(exponent % 2)
                require(R > 0 and R * R >= F(1, q * q) * (1 + F(1, q))**exponent,
                        "Invalid rational radius bound")
                eta = L * gram / (2 * R)
                require(L > 0 and 0 <= eta <= F(1, 2), "Strip sign or monotonicity guard failed")
                require(L * L > 2 * R * T * (1 + upper_x * upper_y * U * U / 4) * (1 - eta * U)**2,
                        "Strip exclusion failed")
            counts[kind] += 1
            maximum_depth = max(maximum_depth, depth)

        visit(case["tree"], (a, b, a, b), 0)
        recomputed = {"projection": counts["projection"], "strip": counts["strip"],
                      "leaves": sum(counts.values()), "maximum_depth": maximum_depth}
        require(case["counts"] == recomputed, "Case statistics do not match the replay")
        require(node_count == 2 * recomputed["leaves"] - 1, "Binary-tree node count mismatch")
        results.append({"q": q, "m": m, "l": ell, **recomputed, "nodes": node_count})

    totals = {str(q): {"pairs": sum(row["q"] == q for row in results),
                      "projection": sum(row["projection"] for row in results if row["q"] == q),
                      "strip": sum(row["strip"] for row in results if row["q"] == q),
                      "maximum_depth": max(row["maximum_depth"] for row in results if row["q"] == q)}
              for q in (2, 3, 4)}
    require(data["case_count"] == len(results), "Top-level case count mismatch")
    require(data["leaf_count"] == sum(row["leaves"] for row in results), "Top-level leaf count mismatch")
    require(isinstance(data["counts_by_quotient"], dict) and
            set(data["counts_by_quotient"]) == {"2", "3", "4"}, "Wrong quotient statistics")
    for row in data["counts_by_quotient"].values():
        require(isinstance(row, dict) and set(row) == {"pairs", "projection", "strip", "maximum_depth"},
                "Wrong quotient count fields")
        for name, value in row.items():
            integer(value, name)
    require(data["counts_by_quotient"] == totals, "Quotient statistics do not match the replay")
    return {"status": "PASS_EXACT_RATIONAL_REPLAY", "cases": len(results),
            "nodes": sum(row["nodes"] for row in results),
            "leaves": sum(row["leaves"] for row in results),
            "counts_by_quotient": totals, "case_results": results}


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def verify_locked(certificate, manifest):
    data = load_json(certificate)
    report = replay(data)
    lock = load_json(manifest)
    require(lock.get("schema_version") == "msc-computation-manifest/1", "Wrong manifest schema")
    require(lock.get("parameters") == PARAMETERS, "Manifest parameters differ from the checked proposition")
    require(lock.get("expected_summary") == {key: report[key] for key in
            ("cases", "nodes", "leaves", "counts_by_quotient")}, "Manifest statistics mismatch")
    require(sha256(certificate) == lock["certificate"]["sha256"], "Certificate checksum mismatch")
    source = (Path(manifest).resolve().parent / lock["manuscript"]["path"]).resolve()
    require(sha256(source) == lock["manuscript"]["sha256"], "Manuscript checksum mismatch")
    scripts = lock.get("script_sha256")
    require(isinstance(scripts, dict) and set(scripts) == set(SCRIPT_NAMES),
            "Manifest must identify every computational source")
    for name, checksum in scripts.items():
        require(sha256(Path(manifest).resolve().parent / name) == checksum,
                f"Computational source checksum mismatch: {name}")
    report["certificate_sha256"] = sha256(certificate)
    report["manuscript_sha256"] = sha256(source)
    report["checker_sha256"] = sha256(__file__)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, default=HERE / "data/pair_trees.json")
    parser.add_argument("--manifest", type=Path, default=HERE / "manifest.json")
    parser.add_argument("--report", type=Path, help="Optional report path; no files are written by default")
    args = parser.parse_args()
    report = verify_locked(args.certificate, args.manifest)
    output = json.dumps(report, indent=2) + "\n"
    if args.report:
        require(args.report.resolve() not in {args.certificate.resolve(), args.manifest.resolve()},
                "A report must not overwrite an input")
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(output, encoding="utf-8")
    print(output, end="")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, RecursionError) as error:
        print(f"VERIFICATION FAILED: {error}", file=sys.stderr)
        raise SystemExit(1)
