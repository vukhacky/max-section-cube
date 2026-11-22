import CubeSections.Analysis.ActualGaussianCost
import CubeSections.Reduction.StrongInduction
import CubeSections.Classical.BallProved
import CubeSections.Geometry.BrunnMinkowski

/-! Composition of the classical branch and strong induction through slab-law
Gaussian couplings. The three reductions use, respectively, slab energy,
frame-law quadratic transport, and regularity of the frame-transported law.
`CubeSections.Main` supplies the proved slab-energy instance. -/

noncomputable section
namespace CubeSections

theorem maximalSection_ge_two_mul_of_slabGaussianEnergy
    (henergy : ∀ k : ℕ, SlabGaussianEnergyStatement k)
    (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k ∧
      (sectionVolume U = sharpValue n k ↔ IsBalancedSection U) := by
  apply maximalSection_ge_two_mul_of_global_estimates
  · intro m j V
    exact angular_bound_of_slabGaussianEnergy (henergy j) V
  · intro m j V hrep
    exact coalesced_incidence_of_slabGaussianEnergy (henergy j) V hrep
  · exact midpointBrunnMinkowski
  · exact hk
  · exact hn

/-- The full main statement follows from slab energy in each dimension,
combining strong induction for `2 * k ≤ n` with the classical range. -/
theorem maximalSections_main_of_slabGaussianEnergy
    (henergy : ∀ k : ℕ, SlabGaussianEnergyStatement k) : MainStatement := by
  refine ⟨?_, ?_, balancedSectionAttains⟩
  · intro n k hk hkn U
    by_cases hn : 2 * k ≤ n
    · exact (maximalSection_ge_two_mul_of_slabGaussianEnergy henergy n k hk hn U).1
    · exact (maximalSection_classical n k hk hkn (by omega) U).1
  · intro n k hk hkn U
    by_cases hn : 2 * k ≤ n
    · exact (maximalSection_ge_two_mul_of_slabGaussianEnergy henergy n k hk hn U).2
    · exact (maximalSection_classical n k hk hkn (by omega) U).2

theorem maximalSections_main_of_frameGaussianQuadraticCost
    (hcost : ∀ k : ℕ, FrameGaussianQuadraticCostStatement k) : MainStatement :=
  maximalSections_main_of_slabGaussianEnergy
    (fun k => slabGaussianEnergy_of_frameGaussianQuadraticCost (hcost k))

theorem maximalSections_main_of_frameTransportRegularDensity
    (hregular : ∀ k : ℕ, FrameTransportRegularDensityStatement k) : MainStatement :=
  maximalSections_main_of_slabGaussianEnergy
    (fun k => slabGaussianEnergy_of_frameTransportRegularDensity (hregular k))

#print axioms maximalSection_ge_two_mul_of_slabGaussianEnergy
#print axioms maximalSections_main_of_slabGaussianEnergy
#print axioms maximalSections_main_of_frameGaussianQuadraticCost
#print axioms maximalSections_main_of_frameTransportRegularDensity
end CubeSections
