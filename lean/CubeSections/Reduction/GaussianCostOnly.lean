import CubeSections.Reduction.TwoInputs
import CubeSections.Geometry.BrunnMinkowski

/-! The main statement as a consequence of the general Gaussian quadratic-cost
proposition. Brunn--Minkowski and the classical sinc inputs are supplied by their
proofs. The unconditional theorem uses the frame-law route in `CubeSections.Main`. -/
noncomputable section
namespace CubeSections

theorem maximalSections_main_of_gaussianCost
    (hTal : ∀ k : ℕ, GaussianQuadraticCostStatement k) : MainStatement :=
  maximalSections_main_of_two_inputs hTal (fun d _ => midpointBrunnMinkowski d)

#print axioms maximalSections_main_of_gaussianCost
end CubeSections
