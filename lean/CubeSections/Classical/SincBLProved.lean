import CubeSections.Analysis.PositiveFunctionalBL
import CubeSections.Classical.SincBLFromFunctional
import CubeSections.Classical.BallInterior
import CubeSections.Classical.Equality

/-! Unconditional specialized sinc Brascamp--Lieb and the resulting classical
cube-section reduction to the strict scalar Ball inequality alone. Functional
BL, Fourier inversion, and the zero-deficit equality argument are all proved.
-/
noncomputable section
namespace CubeSections

theorem sincBrascampLieb : SincBrascampLiebStatement :=
  sincBrascampLieb_of_positiveFunctionalBL positiveFunctionalBL

theorem classicalFourierProductBound : ClassicalFourierProductBound :=
  classicalFourierProductBound_of_sincBrascampLieb sincBrascampLieb

theorem classical_codimension_bound_of_ball
    (hBall : StrictBallSincBound)
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k :=
  classical_codimension_bound_of_sinc_inputs hBall sincBrascampLieb n k hk hkn hn U

theorem classical_equality_iff_of_ball
    (hBall : StrictBallSincBound)
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k) (U : Frame n k) :
    sectionVolume U = sharpValue n k ↔ IsBalancedSection U :=
  classical_equality_iff_of_ball_and_sincBL hBall sincBrascampLieb hk hkn hn U

theorem maximalSection_classical_of_interior
    (hBall : BallSincStrictInteriorStatement)
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k ∧
      (sectionVolume U = sharpValue n k ↔ IsBalancedSection U) :=
  maximalSection_classical_of_sinc_inputs (strictBallSincBound_of_interior hBall)
    sincBrascampLieb n k hk hkn hn U

#print axioms sincBrascampLieb
#print axioms classicalFourierProductBound
#print axioms classical_codimension_bound_of_ball
#print axioms classical_equality_iff_of_ball
#print axioms maximalSection_classical_of_interior
end CubeSections
