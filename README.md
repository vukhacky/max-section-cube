# Maximal sections of the cube

Lean formalization and exact computational supplement for **Maximal sections of the cube**, by Vu Khac Ky.

For integers $1\le k\le n$, write $n=qk+r$, where $0\le r<k$. For every linear isometry $U:\mathbb R^k\to\mathbb R^n$, the main theorem states

$$
\lambda_k\!\left(U^{-1}([-\tfrac12,\tfrac12]^n)\right)
\le \sqrt{q^{k-r}(q+1)^r}.
$$

Equality holds exactly when the range of $U$ is a signed coordinate-block subspace with $k-r$ blocks of size $q$ and $r$ blocks of size $q+1$. These subspaces attain the bound. Volume is the intrinsic Euclidean volume of the section; the equality condition depends on the subspace, not its chosen orthonormal parametrization.

## Contents

| Directory | Purpose |
|---|---|
| [`lean/`](lean/README.md) | Lean 4 source, pinned dependencies, build and theorem-checking tools |
| [`computation/`](computation/README.md) | Exact rational verifiers, certificate data, regeneration, and tests |
| [`manuscript/`](manuscript/README.md) | The mathematical source to which this formalization and the computations are tied |
| [`docs/`](docs/PROOF_MAP.md) | Proof map, formalization scope, and maintenance instructions |
| [`verification/`](verification/README.md) | Recorded verification results and their interpretation |

## Run the computational supplement

From the repository root, with Python 3.10 or later:

```bash
python3 computation/verify.py
python3 computation/regenerate.py --check
python3 computation/check_lean_data.py --lean-dir lean
python3 computation/export_lean.py --check --lean-dir lean
python3 -m unittest discover -s computation/tests -v
```

The supplement uses the Python standard library and exact rational arithmetic. It checks all 19 multiplicity cases for the three small quotients. `regenerate.py --check` reconstructs the certificates and compares them with the committed data. The Lean-data check compares those trees with the concrete expressions used in the formal proof.

The two verification programs named in the manuscript can also be run directly:

```bash
python3 computation/verify_pairs.py
python3 computation/verify_pairs_independent.py
```

The first reproduces the two-dimensional subdivision table; the second subdivides the angle variable as well. Their arithmetic checks are distinct from the Lean proof of checker soundness and its connection to the geometric inequality. See the [computational supplement](computation/README.md) for exact scope and output.

## Check the formal proof

The project pins Lean **4.37.0-rc1** and Mathlib commit
`c47f9ad906c5ec32a953f99911b446cd26dcc123`. With the specified Lean toolchain installed:

```bash
cd lean
lake exe cache get
lake build
```

Then run the theorem and axiom checks:

```bash
python3 scripts/check.py --aggregate
```

[lean/README.md](lean/README.md) also documents using an existing cache at the exact pinned revisions. The repository does not include Lean binaries or Mathlib build outputs.

The four exported declarations are:

| Declaration | Contract |
|---|---|
| `CubeSections.maximalSectionVolume` | Sharp upper bound for every admissible dimension and frame |
| `CubeSections.balancedSectionAttains` | Construction of an attaining balanced section |
| `CubeSections.maximalSectionVolume_eq_iff` | Complete equality classification by the range |
| `CubeSections.maximalSections_main` | The three conclusions together |

Their permitted axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The theorem check verifies both the declared contracts and an independently expanded statement of their mathematical content.

## Scope and reproducibility

The formalization covers the main upper bound, attainment, and equality classification. The manuscript also discusses stability and applications; their inclusion in the manuscript does not assert that every such statement has a separate Lean proof. See [FORMALIZATION.md](docs/FORMALIZATION.md).

The certificate data have one canonical location, `computation/data/pair_trees.json`. The computational manifest binds these data to the manuscript, formulas, and expected subdivision statistics. [`release_manifest.json`](release_manifest.json) records the files belonging to the published source distribution.

For changes to the article or code, follow [MAINTENANCE.md](docs/MAINTENANCE.md). Commit the source changes, regenerated data, and new verification results together so that a reader can identify exactly which computation supports which manuscript revision.

## Citation

Use [`CITATION.cff`](CITATION.cff) for the software citation. When citing a particular computation or formal proof, also identify the repository commit. The manuscript source gives its title, author, and bibliography.
