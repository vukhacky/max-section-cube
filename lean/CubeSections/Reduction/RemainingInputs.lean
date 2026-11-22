import CubeSections.Reduction.StandardInputs
import CubeSections.Classical.BallInterior

/-! Conditional composition using Gaussian transport, midpoint Brunn--Minkowski,
strict sinc for `p > 2`, and specialized functional Brascamp--Lieb. The proved
sinc endpoint and low-dimensional geometry fill the boundary cases.
-/
noncomputable section
namespace CubeSections

theorem maximalSections_main_of_remaining_inputs
    (hTal : ∀ k : ℕ, GaussianQuadraticCostStatement k)
    (hBM : ∀ d : ℕ, 2 ≤ d → MidpointBrunnMinkowski d)
    (hBall : BallSincStrictInteriorStatement)
    (hBL : SincBrascampLiebStatement) : MainStatement :=
  maximalSections_main_of_standard_inputs hTal hBM (strictBallSincBound_of_interior hBall) hBL

#print axioms maximalSections_main_of_remaining_inputs

end CubeSections
