# Updating the manuscript, code, and formal proof

The manuscript, exact certificate data, verifiers, and Lean proof are maintained as source files in one repository. Use a branch for each substantive revision and identify the supporting commit when submitting a manuscript or distributing a source archive.

## Sources of truth

| Item | Authoritative source |
|---|---|
| Mathematical statements and formulas | `manuscript/Maximal_Sections_of_the_Cube_Geometric_Proof.tex` |
| Rational algorithm and certificate format | `computation/` source and `computation/manifest.json` |
| Concrete rational trees | `computation/data/pair_trees.json` |
| Formal theorem contracts | `lean/CubeSections/Semantics.lean` and `lean/target_manifest.json` |
| Lean versions and dependencies | `lean/lean-toolchain`, `lean/lakefile.toml`, `lean/lake-manifest.json` |
| Published source inventory | `release_manifest.json` |

Generated verification output is evidence for a specific input, not a second editable source of truth. Build products and temporary candidate data belong in ignored output directories.

## Editorial manuscript changes

1. Edit the manuscript source and rebuild its PDF locally if needed.
2. Inspect the diff to confirm whether the mathematical statements, formula labels, constants, or verification table changed.
3. Run `python3 computation/refresh_manifest.py --write` only after that review. A hash mismatch must not be resolved by blindly accepting new constants or results.
4. Run the computational checks and repository checks below. Record the revision and its verification results in the same commit.

The repository does not treat a matching hash as a proof that a mathematical edit is valid.

## Algorithm, constants, or certificate changes

Keep proposed changes in candidate files until reviewed. The generator and verifier have separate roles: generation finds a finite subdivision; verification checks the committed witnesses and complete closed-domain coverage.

```bash
python3 computation/verify.py
python3 computation/regenerate.py --check
python3 computation/check_lean_data.py --lean-dir lean
python3 computation/export_lean.py --check --lean-dir lean
python3 -m unittest discover -s computation/tests -v
```

If changing the algorithm intentionally changes the trees, first generate candidates using the options documented in `computation/README.md`. Compare the candidates with the current data, run the independent verifiers and negative tests, and inspect the effect on the manuscript's table and inequalities. Replace the canonical JSON and update its manifest only once the intended changes are understood.

The Lean expressions under `lean/CubeSections/Certificates/Data/` encode the same trees. After changing canonical data, regenerate candidate Lean data using the exporter documented in the computational README, compare it with the committed files, and rerun the data bridge. Changes to a formula or certificate semantics also require updating and checking the corresponding Lean soundness proof; regenerating a `true` result alone does not establish the mathematical conclusion.

## Lean changes

Use the pinned toolchain and dependencies. Build the affected source and check the final contracts:

```bash
cd lean
lake build
python3 scripts/check.py --aggregate
```

See `lean/README.md` for explicit `--lean-bin` and `--packages` paths when reusing an existing environment. Before distributing a new formal proof, perform a fresh project build and run the four-contract gate. Where available, export and externally check the four target proof bodies using the documented checker interface.

A change to `Semantics.lean` or the final theorem types requires explicit mathematical review against the manuscript. The acceptance condition is the original full-domain intrinsic-volume theorem and range-based equality classification; it must not be weakened to accommodate a proof failure.

## Refreshing a distributable source tree

After the intended source changes and verification records are final, run from the repository root:

```bash
python3 tools/release_manifest.py write
python3 tools/check_repository.py
```

The first command explicitly refreshes the source inventory. The second checks it without rewriting it, and rejects modified, missing, unlisted, or inappropriate source files. Review the manifest diff as part of the change.

Commit the manuscript, computation, formal sources, manifests, and verification records together. Use the commit identifier to freeze the version supplied with a paper. Later edits remain ordinary Git commits, so readers can retrieve both the submitted source and subsequent corrections without relying on mutable download names.

## Required publication checks

- Mathematical statements still match the intended theorem and manuscript labels.
- Exact verifiers, regeneration comparison, and Lean-data bridge pass.
- Negative checker tests reject malformed and invalid witnesses.
- Lean builds and the four theorem/axiom checks pass.
- Source inventory and recorded evidence refer to the same files.
