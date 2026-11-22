#!/usr/bin/env python3
"""Check the four fixed MSC contracts and their literal mathematical restatements."""

from pathlib import Path
import argparse
import datetime
import json
import re
import subprocess
import sys
import time

from verification import ROOT, TARGETS, ALLOWED_AXIOMS, check_targets, environment, sha, write_json

LITERAL_CONTRACTS = 'import CubeSections.Main\n\n/-! Literal restatement of intrinsic volume, the sharp value and signed block ranges. -/\n\nnoncomputable section\nopen Set MeasureTheory\n\nnamespace MSCVerification\n\nabbrev V (d : ℕ) := EuclideanSpace ℝ (Fin d)\n\ndef literalVolume {n k : ℕ} (U : V k →ₗᵢ[ℝ] V n) : ℝ :=\n  (volume {x : V k | ∀ i : Fin n, |(U x) i| ≤ (1 : ℝ) / 2}).toReal\n\ndef literalSharp (n k : ℕ) : ℝ :=\n  Real.sqrt ((n / k : ℕ) ^ (k - n % k) * ((n / k : ℕ) + 1) ^ (n % k) : ℝ)\n\ndef literalBalanced {n k : ℕ} (U : V k →ₗᵢ[ℝ] V n) : Prop :=\n  ∃ b : Fin n → Fin k, Function.Surjective b ∧\n    ∃ negative : Fin n → Bool,\n      (∀ j : Fin k,\n        (Finset.univ.filter (fun i => b i = j)).card = n / k ∨\n        (Finset.univ.filter (fun i => b i = j)).card = n / k + 1) ∧\n      Set.range U = {x : V n | ∃ t : Fin k → ℝ,\n        ∀ i : Fin n, x i = (if negative i then (-1 : ℝ) else 1) * t (b i)}\n\ntheorem literalVolume_eq {n k : ℕ} (U : V k →ₗᵢ[ℝ] V n) :\n    literalVolume U = CubeSections.sectionVolume U := rfl\n\ntheorem literalSharp_eq (n k : ℕ) : literalSharp n k = CubeSections.sharpValue n k := by\n  simp only [literalSharp, CubeSections.sharpValue, Nat.cast_mul, Nat.cast_pow,\n    Nat.cast_add, Nat.cast_one]\n\ntheorem literalBalanced_iff {n k : ℕ} (U : V k →ₗᵢ[ℝ] V n) :\n    literalBalanced U ↔ CubeSections.IsBalancedSection U := by\n  constructor\n  · rintro ⟨b, hb, negative, hbal, hrange⟩\n    exact ⟨⟨b, hb, negative⟩, hbal, hrange⟩\n  · rintro ⟨d, hbal, hrange⟩\n    exact ⟨d.block, d.onto, d.negative, hbal, hrange⟩\n\ntheorem bound_as_stated :\n    ∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ U : V k →ₗᵢ[ℝ] V n,\n      literalVolume U ≤ literalSharp n k := by\n  intro n k hk hkn U\n  rw [literalVolume_eq, literalSharp_eq]\n  exact CubeSections.maximalSectionVolume n k hk hkn U\n\ntheorem equality_as_stated :\n    ∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ U : V k →ₗᵢ[ℝ] V n,\n      (literalVolume U = literalSharp n k ↔ literalBalanced U) := by\n  intro n k hk hkn U\n  rw [literalVolume_eq, literalSharp_eq, literalBalanced_iff]\n  exact CubeSections.maximalSectionVolume_eq_iff n k hk hkn U\n\ntheorem attainment_as_stated :\n    ∀ n k : ℕ, 1 ≤ k → k ≤ n → ∃ U : V k →ₗᵢ[ℝ] V n,\n      literalBalanced U ∧ literalVolume U = literalSharp n k := by\n  intro n k hk hkn\n  obtain ⟨U, hbal, hvol⟩ := CubeSections.balancedSectionAttains n k hk hkn\n  exact ⟨U, (literalBalanced_iff U).2 hbal,\n    by simpa only [literalVolume_eq, literalSharp_eq] using hvol⟩\n\nexample : CubeSections.MainStatement := CubeSections.maximalSections_main\n\nend MSCVerification\n'

LITERAL_TARGETS = (
    "MSCVerification.bound_as_stated",
    "MSCVerification.equality_as_stated",
    "MSCVerification.attainment_as_stated",
)


def split_axiom_tokens(values):
    """Split a printed list at commas outside syntactic universe braces."""
    if not values.strip():
        return []
    parts, start, depth = [], 0, 0
    for index, char in enumerate(values):
        if char == "{":
            if depth:
                raise ValueError("Nested braces in a printed axiom name")
            depth = 1
        elif char == "}":
            if not depth:
                raise ValueError("Unmatched brace in a printed axiom name")
            depth = 0
        elif char == "," and not depth:
            parts.append(values[start:index].strip())
            start = index + 1
    if depth:
        raise ValueError("Unclosed universe suffix in a printed axiom name")
    parts.append(values[start:].strip())
    if not all(parts):
        raise ValueError("Empty entry in a printed axiom list")
    return parts


def normalize_axiom_name(token):
    """Remove only a well-formed final Lean universe suffix, retaining the exact name."""
    match = re.fullmatch(
        r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)(?:\.\{([^{}]*)\})?",
        token.strip())
    if match is None:
        raise ValueError("Malformed printed axiom name: " + token)
    name, levels = match.groups()
    if levels is None:
        return name
    # A small fail-closed parser for Lean's printed universe expressions.
    # Levels use parameters/numerals, max/imax, parentheses and + numeral.
    pieces = re.findall(r"[A-Za-z_][A-Za-z0-9_']*|[0-9]+|[(),+]", levels)
    if "".join(pieces) != re.sub(r"\s+", "", levels) or not pieces:
        raise ValueError("Malformed universe suffix: " + token)
    position = 0
    def level():
        nonlocal position
        if position >= len(pieces):
            raise ValueError("Missing universe expression: " + token)
        atom = pieces[position]
        position += 1
        if atom == "(":
            level()
            if position >= len(pieces) or pieces[position] != ")":
                raise ValueError("Unclosed universe parentheses: " + token)
            position += 1
        elif atom in ("max", "imax"):
            level()
            level()
        elif re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*|[0-9]+", atom) is None:
            raise ValueError("Invalid universe expression: " + token)
        while position < len(pieces) and pieces[position] == "+":
            position += 1
            if position >= len(pieces) or not pieces[position].isdigit():
                raise ValueError("Universe successor requires a numeral: " + token)
            position += 1
    level()
    while position < len(pieces) and pieces[position] == ",":
        position += 1
        level()
    if position != len(pieces):
        raise ValueError("Trailing universe syntax: " + token)
    return name


def parse_axioms(output):
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.S)
    if len(reports) != len(re.findall(r"'[^']+' depends on axioms:", output)):
        raise ValueError("Malformed or incomplete axiom report")
    result = {}
    for name, values in reports:
        result.setdefault(name, set()).update(normalize_axiom_name(x) for x in split_axiom_tokens(values))
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        result.setdefault(name, set())
    return result


def accepted_axioms(reports, names):
    return all(name in reports and reports[name] <= ALLOWED_AXIOMS for name in names)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--packages", type=Path)
    parser.add_argument("--aggregate", action="store_true", help="Run the aggregate theorem audit and all five remaining audit-only source files")
    parser.add_argument("--output-dir", type=Path, default=ROOT / ".lake/verification")
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    check_targets()
    lean, env, identity, _ = environment(args.lean_bin, args.packages)
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    source = output / "CheckContracts.lean"
    names = [name for name, _ in TARGETS] + list(LITERAL_TARGETS)
    statements = [f"example : {contract} := {name}" for name, contract in TARGETS]
    statements += [f"#print axioms {name}" for name in names]
    source.write_text(LITERAL_CONTRACTS + "\n" + "\n".join(statements) + "\n")
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    tick = time.monotonic()
    try:
        run = subprocess.run([str(lean), "-j1", "-M6144", str(source)], cwd=ROOT, env=env,
                             capture_output=True, text=True, timeout=args.timeout)
        code, log = run.returncode, run.stdout + run.stderr
    except subprocess.TimeoutExpired as error:
        def decode(value):
            return value.decode(errors="replace") if isinstance(value, bytes) else value or ""
        code, log = 124, decode(error.stdout) + decode(error.stderr) + "\nCONTRACT_CHECK_TIMEOUT\n"
    (output / "contracts.log").write_text(log)
    axioms = parse_axioms(log)
    passed = code == 0 and accepted_axioms(axioms, names)
    result = {"schema": "msc-contract-check/1", "status": "PASS" if passed else "FAILED",
              "compiler_exit_code": code, "environment": identity,
              "started_utc": started, "seconds": time.monotonic() - tick,
              "targets": [name for name, _ in TARGETS], "literal_targets": list(LITERAL_TARGETS),
              "axioms": {name: sorted(values) for name, values in axioms.items()},
              "check_source_sha256": sha(source), "log_sha256": sha(output / "contracts.log"),
              "interpretation": "Compiler-checked contract inhabitation and axiom summaries; optional external_check.py checks exported proof bodies."}
    write_json(output / "contracts.json", result)
    print(json.dumps(result, indent=2))
    if not passed:
        return 1
    if args.aggregate:
        aggregate = ROOT / "CubeSections/CheckpointAudit.lean"
        tick = time.monotonic()
        run = subprocess.run([str(lean), "-j1", "-M6144", str(aggregate)], cwd=ROOT, env=env,
                             capture_output=True, text=True, timeout=args.timeout)
        log = run.stdout + run.stderr
        (output / "aggregate.log").write_text(log)
        count = re.search(r"MSC_AUDIT_ACCEPTED_THEOREMS=(\d+)", log)
        passed = run.returncode == 0 and count is not None
        result = {"status": "PASS" if passed else "FAILED", "compiler_exit_code": run.returncode,
                  "selected_public_theorem_count": int(count.group(1)) if count else None,
                  "source_sha256": sha(aggregate), "log_sha256": sha(output / "aggregate.log"),
                  "seconds": time.monotonic() - tick}
        write_json(output / "aggregate.json", result)
        print(json.dumps(result, indent=2))
        if not passed:
            return 1
        audit_sources = (
            "CubeSections/Analysis/BranchAxioms.lean",
            "CubeSections/Certificates/Audit.lean",
            "CubeSections/Classical/Audit.lean",
            "CubeSections/Geometry/Audit.lean",
            "CubeSections/Integer/Audit.lean",
        )
        audited = []
        for relative in audit_sources:
            audit_source = ROOT / relative
            before = sha(audit_source)
            tick = time.monotonic()
            try:
                run = subprocess.run([str(lean), "-j1", "-M6144", str(audit_source)],
                                     cwd=ROOT, env=env, capture_output=True,
                                     text=True, timeout=args.timeout)
                code, log = run.returncode, run.stdout + run.stderr
            except subprocess.TimeoutExpired as error:
                def decode(value):
                    return value.decode(errors="replace") if isinstance(value, bytes) else value or ""
                code, log = 124, decode(error.stdout) + decode(error.stderr) + "\nAUDIT_SOURCE_TIMEOUT\n"
            unchanged = sha(audit_source) == before
            reports = parse_axioms(log)
            permitted = all(axioms <= ALLOWED_AXIOMS for axioms in reports.values())
            passed = code == 0 and unchanged and permitted
            receipt_path = output / "audit_modules" / Path(relative).with_suffix(".json")
            receipt_path.parent.mkdir(parents=True, exist_ok=True)
            log_path = receipt_path.with_suffix(".log")
            log_path.write_text(log)
            record = {"source": relative, "status": "PASS" if passed else "FAILED",
                      "compiler_exit_code": code, "source_sha256": before,
                      "source_unchanged": unchanged, "log_sha256": sha(log_path),
                      "seconds": time.monotonic() - tick,
                      "printed_axiom_reports": len(reports),
                      "printed_axioms_permitted": permitted,
                      "receipt": str(receipt_path.relative_to(output))}
            write_json(receipt_path, record)
            audited.append(record)
            write_json(output / "additional_audits.json", {
                "status": "PASS" if passed and len(audited) == len(audit_sources)
                          else "RUNNING" if passed else "FAILED",
                "expected_sources": list(audit_sources), "checked": audited})
            print(json.dumps(record, indent=2))
            if not passed:
                return 1
        return 0
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        print(f"Contract check error: {error}", file=sys.stderr)
        raise SystemExit(1)
