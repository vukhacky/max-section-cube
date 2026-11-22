# Verification records

This directory records completed local verification of the source distribution on **2026-11-23 (UTC+07:00)**. Machine-readable execution timestamps use UTC. Commands and results are tied to exact input hashes; generated build objects and large proof exports are not part of the source repository.

[`results.json`](results.json) summarizes the source build, final contract checks, rational verification, and external proof-body check. [`release_manifest.json`](../release_manifest.json) at the repository root records the distributed source files. The formalization's mathematical scope is described in [`docs/FORMALIZATION.md`](../docs/FORMALIZATION.md).

## Recorded results

| Check | Completed result | Evidence |
|---|---|---|
| Fresh Lean source compilation | 349 modules, each compiler exit code 0; no initial project objects | [`lean_build.json`](lean_build.json) |
| Exact theorem contracts | All four contracts and three literal mathematical restatements accepted; only `propext`, `Classical.choice`, and `Quot.sound` | [`contract_check.json`](contract_check.json), [compiler output](contract_check.log) |
| Additional Lean source coverage | Six audit-only sources accepted, including the aggregate audit of 3,012 selected public project theorems; 355 project source files checked in total | [`audit_sources.json`](audit_sources.json) |
| Actual proof dependency graph | 87,154 declarations and 18,514,315 expressions reachable from the four main targets; exactly the three standard axioms; no unsafe or partial dependencies | [`external_graph.json`](external_graph.json) |
| External proof type check | Nanoda checked all 87,154 exported declarations with no errors; exit code 0 and empty standard error | [`external_check.json`](external_check.json), [checker output](external_checker.stdout.log), [rendered signatures](external_signatures.txt) |
| External checker controls | A valid proof was accepted; an incorrect proof body and an unapproved axiom were rejected for their intended reasons | [`external_controls.json`](external_controls.json) |
| Rational computation | 19 certificate trees, 6,795 nodes, 3,407 leaves; deterministic data and 101 Lean data files reproduced; independent three-dimensional cover checked | [`computation/verification.json`](../computation/verification.json) |
| Regression tests | 23 computation tests and 18 Lean-tool tests each passed in normal and optimized Python; 37 repository-tool tests passed | [`tool_tests.json`](tool_tests.json), [computation results](../computation/verification.json) |

The fresh 349-module build used dependency-ordered direct compiler invocations. The record preserves each module's source and output hashes, imported object hashes, command, exit code, and timing. Its dispatcher was distinct from the public `lean/scripts/build.py` reproduction command. The public builder was separately checked with a real-compiler fixture covering initial compilation, valid cache reuse, output tampering, and recompilation; that fixture is explicitly distinguished from the MSC build in `tool_tests.json`.

## Interpreting the checks

- **Fresh Lean compilation** checks the project modules with the pinned compiler. Cached dependency objects may be used, as described by the environment record.
- **The contract gate** checks the four theorem types and an independently expanded intrinsic-volume and balanced-range formulation. It also checks the permitted axiom dependencies.
- **The aggregate audit** inspects the selected project theorem declarations. Its count is not the number of all transitive Lean and Mathlib dependencies.
- **An exported-body graph check** follows actual declaration types and values, rather than imported axiom summaries. It is a dependency inventory, not a proof type checker.
- **The external type checker** checks the same exported bodies under the stated axiom policy. Its record identifies the input export, exporter and checker binaries, versions, and logical settings.
- **Python verification** checks exact rational witnesses and data correspondence. The mathematical use of those witnesses additionally relies on the Lean soundness, coverage, and geometric bridge theorems.

The compiler, exporter, checker, and operating environment remain software dependencies. A successful check is not a compiler bootstrap or independent authentication of the binary distribution. Reusing dependency objects also does not establish a complete source/object rebuild of every Mathlib definition. The external record identifies nanoda 0.4.31 by its observed version and exact binary hash; no independently established nanoda source commit is asserted.

These checks concern the four main contracts. They do not assert a formalization of every auxiliary manuscript statement, stability result, or application. The records describe local executions; inspect [GitHub Actions](https://github.com/vukhacky/max-section-cube/actions) separately for a particular remote commit.

## Reproduction

Follow [`lean/README.md`](../lean/README.md) for the formal build and optional external checker, and [`computation/README.md`](../computation/README.md) for the rational verification. Store local outputs under an ignored directory such as `verification/runs/`.

Recorded machine paths are normalized to `${REPOSITORY_ROOT}`, `${MSC_LEAN_BIN}`, `${MSC_LEAN_RUNTIME}`, and `${MSC_PACKAGES}`, or to paths relative to the recorded working directory. These mean the repository root, pinned executable directory, its parent runtime directory, and pinned package directory. Actual command flags, logical settings, hashes, exit codes, and timings are retained. Simplified reproduction commands are separate fields. The contract compiler log, checker standard output, and rendered signatures are copied unchanged.

From the repository root, check that the distributed files match their inventory:

```bash
python3 tools/check_repository.py
```

The optional export is approximately one gigabyte for the recorded theorem closure. It is regenerated from the checked source; its hash and the checker result are recorded instead of committing the raw export.
