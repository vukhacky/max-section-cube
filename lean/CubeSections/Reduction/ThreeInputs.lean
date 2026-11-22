import CubeSections.Reduction.RemainingInputs
import CubeSections.Classical.SincBLProved

/-! Conditional composition from Gaussian quadratic transport, midpoint
Brunn--Minkowski and strict scalar sinc, using the proved functional-BL input. -/
noncomputable section
namespace CubeSections

theorem maximalSections_main_of_three_inputs
    (hTal : ∀ k : ℕ, GaussianQuadraticCostStatement k)
    (hBM : ∀ d : ℕ, 2 ≤ d → MidpointBrunnMinkowski d)
    (hBall : BallSincStrictInteriorStatement) : MainStatement :=
  maximalSections_main_of_remaining_inputs hTal hBM hBall sincBrascampLieb

#print axioms maximalSections_main_of_three_inputs
end CubeSections
