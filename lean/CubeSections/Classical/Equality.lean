import CubeSections.Classical.SincBrascampLieb
import CubeSections.Analysis.ZeroDeficitCoupling

/-! Classical equality classification from the strict scalar sinc bound and
specialized functional BL. Zero-deficit transport constructs the Gaussian
coupling directly. The sinc inputs of this reduction are proved in
`Classical.BallProved` and `Classical.SincBLProved`. -/

noncomputable section
namespace CubeSections

theorem classical_equality_iff_of_ball_and_sincBL
    (hBall : StrictBallSincBound) (hBL : SincBrascampLiebStatement)
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2 * k) (U : Frame n k) :
    sectionVolume U = sharpValue n k ↔ IsBalancedSection U := by
  constructor
  · intro heq
    by_cases hnk : n = k
    · subst n
      exact fullDimension_isBalancedSection U (by omega)
    have hFourier := classicalFourierProductBound_of_sincBrascampLieb hBL
    have hhalf := half_leverage_of_classical_equality hBall hFourier hk (by omega) hn U heq
    have hc := classicalLeverageDichotomy_of_sinc_equality hBall hFourier hk hkn hn U hhalf heq
    have hδ := slabDeficit_zero_of_classicalLeverage_equality hk hkn hn U hc heq
    exact (classicalBlock_classification_of_zeroAngular hk U hc
      (gramAngularDefect_eq_zero_of_slabDeficit_zero U hδ)).1
  · exact sectionVolume_eq_sharp_of_isBalancedSection U

theorem maximalSection_classical_of_sinc_inputs
    (hBall : StrictBallSincBound) (hBL : SincBrascampLiebStatement)
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2 * k) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k ∧
      (sectionVolume U = sharpValue n k ↔ IsBalancedSection U) :=
  ⟨classical_codimension_bound_of_sinc_inputs hBall hBL n k hk hkn hn U,
    classical_equality_iff_of_ball_and_sincBL hBall hBL hk hkn hn U⟩

#print axioms classical_equality_iff_of_ball_and_sincBL
#print axioms maximalSection_classical_of_sinc_inputs

end CubeSections
