# From the manuscript to the formal proof

Paths in this table are relative to `lean/CubeSections/`. The manuscript labels are stable LaTeX labels, so the correspondence does not depend on pagination.

| Mathematical component | Manuscript label | Lean entry points |
|---|---|---|
| Main theorem and balanced value | `thm:full-balanced-value`, `eq:balanced-target` | `Semantics.lean`, `Main.lean` |
| Signed block construction and attainment | `eq:balanced-target` | `Geometry/Blocks.lean`, `Geometry/BlockVolume.lean`, `Integer/Balanced.lean`, `Geometry/Attainment.lean` |
| Frame and Gram identities | `sec:frames` | `Geometry/RowVectors.lean`, `LinearAlgebra/Gram.lean`, `LinearAlgebra/Projection.lean` |
| Determinant entropy and transport | `lem:core-entropy-coupling`, `eq:core-entropy-decomposition` | `Analysis/TransportEntropy.lean`, `Analysis/ActualGaussianCostProved.lean` |
| Determinant remainder and angles | `lem:pairwise-determinant-production`, `thm:incidence` | `Analysis/GlobalTransportEnergy.lean`, `Analysis/ActualAngular.lean` |
| Integer packing and row variations | `sec:integer-packing`, `sec:extremal-comparison` | `Integer/`, `Geometry/RowChanges.lean`, `Geometry/Variational.lean` |
| Pair-coordinate fibers and coarea | `sec:extremal-comparison` | `Geometry/PairCoarea.lean`, `Geometry/FiberDensityCap.lean`, `Geometry/ClassDensityInduction.lean` |
| Finite rational comparison | `prop:edge-pay`, `sec:comparisons` | `Certificates/Checker.lean`, `Certificates/Coverage.lean`, `Certificates/Soundness.lean`, `Certificates/AllPairsData.lean` |
| Actual geometric input to certificates | `prop:edge-pay` | `Certificates/DensityStripBridge.lean`, `Certificates/GeometricStripBridge.lean`, `Certificates/ActualGroupedComparison.lean` |
| Strong dimension induction | `thm:full-balanced-value` | `Reduction/StrongInduction.lean`, `Reduction/ActualTransport.lean` |
| Classical codimension range | `thm:full-balanced-value` | `Classical/BallProved.lean`, `Classical/SincBLProved.lean`, `Classical/Equality.lean` |
| Equality and signed block reconstruction | `thm:full-balanced-value` | `Geometry/Rigidity.lean`, `Geometry/SignedBlocks.lean`, `Classical/CodimensionRigidity.lean` |

The import chain starting at `Main.lean` determines which results are used by the final theorem. The audit modules are additional verification entry points and are not mathematical hypotheses.

For the exact certificate formulas, parameters, and table counts, see `computation/manifest.json` and `computation/README.md`.
