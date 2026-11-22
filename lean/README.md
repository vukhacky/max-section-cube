# Lean formalization

The entry point is [`CubeSections/Main.lean`](CubeSections/Main.lean). Its four exported theorems prove the sharp bound, attainment, range-based equality characterization, and their conjunction for every `1 ≤ k ≤ n`. The mathematical definitions are in [`CubeSections/Semantics.lean`](CubeSections/Semantics.lean). [`target_manifest.json`](target_manifest.json) fixes the four declaration/contract pairs and the permitted foundational axioms.

| Declaration | Contract |
|---|---|
| `CubeSections.maximalSectionVolume` | `UpperBoundStatement` |
| `CubeSections.balancedSectionAttains` | `AttainmentStatement` |
| `CubeSections.maximalSectionVolume_eq_iff` | `EqualityStatement` |
| `CubeSections.maximalSections_main` | `MainStatement` |

## Environment

- Lean **4.37.0-rc1**, commit `0b77e12952ad39077d80d8bd6b66d601f225c321`.
- Mathlib commit `c47f9ad906c5ec32a953f99911b446cd26dcc123`.
- All other revisions are fixed by `lake-manifest.json`.
- Python **3.10 or newer**, using only its standard library, for verification scripts.

Install [elan](https://github.com/leanprover/elan) if Lean is not already available. Keep `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` together. Do not replace the manifest with a newly resolved dependency set when reproducing this version.

## Standard Lake build

From this directory:

```bash
lake exe cache get
lake build
python3 scripts/check.py --aggregate
```

The first command obtains the dependency cache selected by the pinned manifest. If that exact cache is already present, it can be reused. `lake build` checks the Lean library. The last command additionally asks Lean to inhabit each of the four fixed contracts and literal restatements of the volume, quotient/remainder value, and signed block range. It rejects an absent axiom report or any axiom other than `propext`, `Classical.choice`, and `Quot.sound`. `--aggregate` checks the selected public project theorems with `CubeSections/CheckpointAudit.lean`, then directly compiles the five additional audit-only sources: `Analysis/BranchAxioms.lean`, `Certificates/Audit.lean`, `Classical/Audit.lean`, `Geometry/Audit.lean`, and `Integer/Audit.lean` under `CubeSections/`. These invocations do not write `.olean` objects and fail the command on a compiler error, timeout, source change, or unapproved printed axiom. Together with the 349-module main import closure, the six audit sources cover all **355 checked-in Lean sources** in this release.

Generated reports are written to `.lake/verification/`; they are not source files. `contracts.json` and `aggregate.json` report only the results of their corresponding invocations. `additional_audits.json` and the per-source JSON/log pairs in `audit_modules/` record the five remaining audit-source checks. Compiling a proposition definition alone is never accepted as proving it.

## Serial build with explicit, existing dependencies

On Linux or macOS, the included builder can use an already installed toolchain and a separate read-only package cache:

```bash
MSC_LEAN_BIN=/absolute/path/to/lean-4.37.0-rc1-linux/bin
MSC_PACKAGES=/absolute/path/to/pinned/.lake/packages
python3 scripts/build.py --lean-bin "$MSC_LEAN_BIN" --packages "$MSC_PACKAGES" --fresh
python3 scripts/check.py --lean-bin "$MSC_LEAN_BIN" --packages "$MSC_PACKAGES" --aggregate
```

These are directory parameters, not required filesystem locations. The builder verifies the compiler version and commit, dependency revisions and clean source checkouts, then compiles the import closure of `CubeSections` one module at a time. It never downloads, modifies or rebuilds dependency packages. This path is useful when reusing an existing correct cache or limiting concurrent compiler memory use.

`--fresh` ignores all project receipts and recompiles every module. Without `--fresh`, reuse requires the current source, direct imported object hashes, compiler context, package pins, and the module's **own output hash** to match one successful producing receipt. Local dependency input fingerprints are propagated transitively, so an ancestor change invalidates downstream reuse even if an intermediate compiled object's bytes happen to stay unchanged. Failed or interrupted compilations do not replace a previously produced object. Receipts and per-module compiler logs are under `.lake/verification/modules/`.

The environment check identifies package revisions and directly imported object bytes. It does not rebuild every dependency definition from source or authenticate the compiler bootstrap. For a direct check of the selected transitive proof bodies, use the optional procedure below.

## Optional external proof check

The independent-check procedure requires a compatible `leanexport` executable (export format 3.1.0) and **nanoda 0.4.31**. They are separate prerequisites and are not downloaded by these scripts. Pass their executable paths if they are not beside `lean`:

```bash
python3 scripts/external_check.py smoke --exporter /path/to/leanexport --checker /path/to/nanoda
python3 scripts/external_check.py export --exporter /path/to/leanexport
python3 scripts/external_check.py graph
python3 scripts/external_check.py nanoda --checker /path/to/nanoda --timeout 3600
```

Add the same `--lean-bin` and `--packages` arguments as above when using a separate installation. Run stages serially after compilation. Use a new `--output-dir` to retain evidence from another run; the default is `.lake/verification/external/`.

The export selects exactly the four public theorem bodies and their dependencies from `CubeSections.Main`. The graph diagnostic traverses actual type/value expressions and displays the actual axiom signatures; it is **not** a type checker. Nanoda checks the exported declarations with only the three standard axioms permitted and hard rejection of other axioms, including unused ones. The smoke stage requires acceptance of a valid proof, type rejection of a deliberately altered proof body, and rejection of an added unapproved axiom. A timeout, input-format error, or resource failure is not successful verification.

The export can be about 1 GB and is generated locally rather than committed. `targets_nanoda.receipt.json`, the complete checker output, `targets_graph.json`, and the rendered signatures identify the result of that particular run. A `#print axioms` report uses Lean's imported axiom metadata; the actual-body graph and external type check are additional verification steps.

## Changing the formalization

Use ordinary source commits for changes. Keep theorem statements fixed unless the mathematical specification is intentionally revised and documented. After modifying Lean source, run the build and contract check again. If certificate data change, first run the computational supplement's generator/verifier and Lean-data consistency check, then compile and check the formalization. The workflow at `../.github/workflows/verify.yml` runs computational validation and a fresh serial proof build; its existence does not by itself assert that a CI run has succeeded.

The verification tool regressions can be run independently:

```bash
python3 -m unittest discover -s scripts/tests -v
```
