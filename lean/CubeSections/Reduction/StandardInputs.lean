import CubeSections.Reduction.AnalyticInputs
import CubeSections.Reduction.LowDimension
import CubeSections.Geometry.MidpointLowDimension
import CubeSections.Classical.Equality

/-! Conditional composition using Gaussian quadratic transport, midpoint
Brunn--Minkowski in dimensions at least two, strict scalar sinc and specialized
functional Brascamp--Lieb.
-/

noncomputable section
namespace CubeSections

theorem maximalSection_le_three_of_gaussianCost
    (hTal : ∀ j : ℕ, GaussianQuadraticCostStatement j)
    (n k : ℕ) (hk : 1 ≤ k) (hk₃ : k ≤ 3) (hn : 2 * k ≤ n) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k ∧
      (sectionVolume U = sharpValue n k ↔ IsBalancedSection U) := by
  apply maximalSection_le_three_of_global_estimates
  · intro m j V
    exact angular_bound_of_slabGaussianEnergy (slabGaussianEnergy_of_gaussianQuadraticCost (hTal j)) V
  · intro m j V hrep
    exact coalesced_incidence_of_slabGaussianEnergy
      (slabGaussianEnergy_of_gaussianQuadraticCost (hTal j)) V hrep
  · exact hk
  · exact hk₃
  · exact hn

/-- The full main statement, conditional on the four displayed analytic propositions. -/
theorem maximalSections_main_of_standard_inputs
    (hTal : ∀ k : ℕ, GaussianQuadraticCostStatement k)
    (hBM : ∀ d : ℕ, 2 ≤ d → MidpointBrunnMinkowski d)
    (hBall : StrictBallSincBound)
    (hBL : SincBrascampLiebStatement) : MainStatement := by
  have hBMall := midpointBrunnMinkowski_of_ge_two hBM
  refine ⟨?_, ?_, balancedSectionAttains⟩
  · intro n k hk hkn U
    by_cases hn : 2 * k ≤ n
    · exact (maximalSection_ge_two_mul_of_analytic_inputs hTal hBMall n k hk hn U).1
    · exact (maximalSection_classical_of_sinc_inputs hBall hBL n k hk hkn (by omega) U).1
  · intro n k hk hkn U
    by_cases hn : 2 * k ≤ n
    · exact (maximalSection_ge_two_mul_of_analytic_inputs hTal hBMall n k hk hn U).2
    · exact (maximalSection_classical_of_sinc_inputs hBall hBL n k hk hkn (by omega) U).2

#print axioms maximalSection_le_three_of_gaussianCost
#print axioms maximalSections_main_of_standard_inputs

end CubeSections
