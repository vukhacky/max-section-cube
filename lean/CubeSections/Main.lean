import CubeSections.Analysis.ActualGaussianCostProved
import CubeSections.Reduction.ActualTransport

/-! The four maximal-section theorems: upper bound, attainment, equality
classification, and their conjunction. The proof combines the frame-law Gaussian
transport estimates with strong induction on the section dimension.
`Semantics.lean` specifies intrinsic volume and the signed-block range condition. -/

noncomputable section
namespace CubeSections

/-- The full maximal-section theorem, including attainment and every equality case. -/
theorem maximalSections_main : MainStatement :=
  maximalSections_main_of_slabGaussianEnergy slabGaussianEnergy

/-- The sharp upper bound for every `1 ≤ k ≤ n` and every isometric frame. -/
theorem maximalSectionVolume : UpperBoundStatement :=
  maximalSections_main.1

/-- Equality is exactly the signed balanced coordinate-block range condition. -/
theorem maximalSectionVolume_eq_iff : EqualityStatement :=
  maximalSections_main.2.1

#print axioms maximalSectionVolume
#print axioms balancedSectionAttains
#print axioms maximalSectionVolume_eq_iff
#print axioms maximalSections_main

end CubeSections
