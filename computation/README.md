# Exact computations for maximal sections of the cube

This supplement verifies the finite pair comparison in Proposition
`prop:edge-pay` and Appendix `sec:comparisons` of
[`Maximal_Sections_of_the_Cube_Geometric_Proof.tex`](../manuscript/Maximal_Sections_of_the_Cube_Geometric_Proof.tex).
It covers all 19 unordered multiplicity types
$q\in\{2,3,4\}$, $1\le m\le\ell\le q$, on the full closed square
$[1/(q+1),1/q]^2$, with the strict surplus $1/4000$.

**Requirements:** Python 3.10 or later; only the Python standard library is used.
No floating-point arithmetic, numerical optimization, or external solver enters
the verification. Run the following commands from the repository root:

```bash
python3 computation/verify.py
python3 computation/regenerate.py --check
python3 computation/verify_pairs.py
python3 computation/verify_pairs_independent.py
python3 -m unittest discover -s computation/tests -v
```

All commands return a nonzero exit status on failure. They do not modify tracked
files. `verify.py --report /path/to/report.json` optionally saves its output.

## What is checked

`verify.py` reads the canonical data in `data/pair_trees.json`. Every split has
exactly two closed children meeting at the rational midpoint; the root domain
and every inherited rectangle are checked. Each leaf recomputes its own strict
inequality. Stored counts, signs, or acceptance flags are never substitutes for
these checks. The rational encoding is reduced `numerator/positive_denominator`.
Malformed objects, duplicated JSON keys, float/bool substitutions for integer
fields, missing cases, missing children, and unsupported witnesses are rejected.

The two leaf types implement the manuscript formulas:

- **Projection:** the complementary Gram minor gives a lower bound for
  $v=\sin^2\theta$; the checker verifies
  $3v^2>5\{SK(15+v)\}^2$.
- **Strip:** a rational half-angle threshold $T$ separates angles handled by
  the angular test from those excluded by two-row replacement. For $T<1$, the
  upper-angle witness is checked; $T=1$ includes the full half-angle interval.
  The positivity and monotonicity hypotheses are checked before the strict strip
  inequality is accepted.

The curvature bound, monotonicity, geometric hypotheses, and implication from
these rational inequalities to Proposition `prop:edge-pay` are mathematical
arguments in the manuscript. Their formal counterparts are in
`lean/CubeSections/Certificates`. A Python success message alone is not a Lean
proof and does not prove the entire maximal-section theorem independently of
those arguments.

## Reproduction and independent implementations

| Program | Role |
|---|---|
| `verify_pairs.py` | The two-dimensional recursion cited by the manuscript; computes the table without reading stored trees |
| `verify_pairs_independent.py` | A separate three-dimensional subdivision of squared lengths and half-angle |
| `regenerate.py` | Deterministically constructs the canonical binary trees, then subjects them to `verify.py` |
| `verify.py` | An independent implementation of the rational leaf formulas and complete tree replay; imports no generator |
| `check_lean_data.py` | Compares stored trees with concrete Lean data, expanding chunk files |
| `export_lean.py` | Regenerates candidate Lean arithmetic proofs from the checked JSON trees |

The first two programs are preserved byte for byte from the manuscript supplement.
They use different covers and therefore have different terminal counts. The
three-dimensional program is an independent rational cross-check; the Lean
certificate development uses the two-dimensional trees.

The canonical two-dimensional result is:

| $q$ | Multiplicity types | Projection leaves | Strip leaves | Maximum depth |
|---:|---:|---:|---:|---:|
| 2 | 3 | 2,606 | 531 | 18 |
| 3 | 6 | 49 | 93 | 8 |
| 4 | 10 | 28 | 100 | 6 |
| **Total** | **19** | **2,683** | **724** | **18** |

There are **3,407 leaves and 6,795 nodes**. The independent three-dimensional
cover has **10,257 terminal boxes**, maximum depth **28**. The checked-in
`verification.json` records observed reproduction results and source hashes.

## Correspondence with Lean

```bash
python3 computation/check_lean_data.py --lean-dir lean
python3 computation/export_lean.py --check --lean-dir lean
```

The first command compares each tree and parameter triple with the generated
Lean declarations, including all chunk references. It is intentionally a small
parser for the generated data syntax, not a general Lean parser. Unrecognized
tree expressions are rejected. The second command regenerates all 101 Lean data
files in a temporary directory and requires byte-identical output. Neither
command substitutes for compiling the Lean proofs; follow the root reproduction
instructions for that step.

`data/pair_trees.json` is the sole canonical JSON certificate. Generated Lean
files are the proof-carrying representation checked by Lean, not a separately
maintained alternative data set.

## Revising the manuscript or code

Use Git commits to keep the manuscript, programs, certificate data, and formal
proofs synchronized. `manifest.json` records the manuscript and certificate
hashes, fixed mathematical parameters, equation labels, expected counts, and
computational source hashes. These hashes establish which bytes were checked;
they do not certify a new mathematical argument after an edit.

For an editorial manuscript change or implementation refactor:

1. Review the diff and retain the proposition, domain, constants, and strictness.
2. Run `regenerate.py --check`, both manuscript programs, and the tests.
3. Run `python3 computation/refresh_manifest.py --write` to record the reviewed
   manuscript/source bytes. This command first performs the full exact replay.
4. Run `verify.py`, `check_lean_data.py`, `export_lean.py --check`, and the
   repository verification commands. Commit the related changes together.

When a certificate genuinely changes, generate a candidate without replacing
the accepted data:

```bash
python3 computation/regenerate.py --output /tmp/msc-pair-trees-candidate.json
python3 computation/export_lean.py --certificate /tmp/msc-pair-trees-candidate.json \
  --output /tmp/msc-lean-data-candidate
```

Review the resulting diffs, then update the canonical files explicitly. Compile
all affected Lean data and dependent modules before accepting the change. If a
mathematical formula or parameter changes, both independent verification paths
and the corresponding analytic/formal soundness arguments must be reviewed;
refreshing a checksum is insufficient. The programs deliberately provide no
command-line option that silently weakens the fixed surplus or narrows the case
set.

## Data and trust boundaries

Tree metadata contain no acceptance premise: all arithmetic is recomputed.
`manifest.json` is a provenance lock. `verification.json` is an observed execution
summary, not a checker input. The rejection tests exercise invalid covers,
incorrect leaf witnesses, malformed encodings, and a changed Lean tree. They also
run successfully with Python optimization enabled; validation does not rely on
removable `assert` statements.
