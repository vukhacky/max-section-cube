import CubeSections.Reduction.StrongInduction
import CubeSections.Analysis.SlabEnergyFromCost
import CubeSections.Classical.CodimensionReduction

/-! Conditional composition from Gaussian transport, midpoint Brunn--Minkowski,
strict scalar sinc and the Fourier product bound. The theorem arguments specify
each analytic input explicitly; `CubeSections.Main` gives the unconditional
maximal-section result through the frame-law transport route.
-/

noncomputable section
namespace CubeSections

theorem maximalSection_ge_two_mul_of_analytic_inputs
    (hTal : ∀ k : ℕ, GaussianQuadraticCostStatement k)
    (hBM : ∀ d : ℕ, MidpointBrunnMinkowski d)
    (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k ∧
      (sectionVolume U = sharpValue n k ↔ IsBalancedSection U) := by
  apply maximalSection_ge_two_mul_of_global_estimates
  · intro m j V
    exact angular_bound_of_slabGaussianEnergy (slabGaussianEnergy_of_gaussianQuadraticCost (hTal j)) V
  · intro m j V hrep
    exact coalesced_incidence_of_slabGaussianEnergy
      (slabGaussianEnergy_of_gaussianQuadraticCost (hTal j)) V hrep
  · exact hBM
  · exact hk
  · exact hn

/-- The full main statement, conditional on the four displayed analytic propositions. -/
theorem maximalSections_main_of_analytic_inputs
    (hTal : ∀ k : ℕ, GaussianQuadraticCostStatement k)
    (hBM : ∀ d : ℕ, MidpointBrunnMinkowski d)
    (hBall : StrictBallSincBound)
    (hFourier : ClassicalFourierProductBound) : MainStatement := by
  refine ⟨?_, ?_, balancedSectionAttains⟩
  · intro n k hk hkn U
    by_cases hn : 2 * k ≤ n
    · exact (maximalSection_ge_two_mul_of_analytic_inputs hTal hBM n k hk hn U).1
    · exact classical_codimension_bound_of_analytic_inputs hBall hFourier n k hk hkn (by omega) U
  · intro n k hk hkn U
    by_cases hn : 2 * k ≤ n
    · exact (maximalSection_ge_two_mul_of_analytic_inputs hTal hBM n k hk hn U).2
    · exact classical_equality_iff_of_analytic_inputs hBall hFourier hk hkn (by omega) U 20
        (angular_bound_of_slabGaussianEnergy (slabGaussianEnergy_of_gaussianQuadraticCost (hTal k)) U)

#print axioms maximalSection_ge_two_mul_of_analytic_inputs
#print axioms maximalSections_main_of_analytic_inputs

end CubeSections
