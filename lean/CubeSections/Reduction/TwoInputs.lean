import CubeSections.Reduction.ThreeInputs
import CubeSections.Classical.BallProved

/-! Conditional composition from Gaussian quadratic transport and midpoint
Brunn--Minkowski in dimensions at least two, using the proved sinc estimates. -/
noncomputable section
namespace CubeSections

theorem maximalSections_main_of_two_inputs
    (hTal : ∀ k : ℕ, GaussianQuadraticCostStatement k)
    (hBM : ∀ d : ℕ, 2 ≤ d → MidpointBrunnMinkowski d) : MainStatement :=
  maximalSections_main_of_three_inputs hTal hBM ballSincStrictInterior

#print axioms maximalSections_main_of_two_inputs
end CubeSections
