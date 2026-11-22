import CubeSections.Classical.BallNearTwo
import CubeSections.Classical.BallThreeBound
import CubeSections.Classical.BallLargeP
import CubeSections.Classical.SincBLProved

/-! The full strict scalar Ball sinc inequality and the unconditional classical
cube-section upper bound with equality classification. The strict interval
(2,3] uses the quantitative cubic estimate I3<7/9; [3,4] uses exact moments
and Holder; [4,infinity) uses a Gaussian core and an exact power tail.
All scalar integrability and endpoint normalization are proved.
-/
noncomputable section
namespace CubeSections

/-- The normalized sinc integral is strictly below the sharp value for every
real exponent p>2, with no analytic input hypothesis. -/
theorem ballSincStrictInterior : BallSincStrictInteriorStatement := by
  intro p hp
  by_cases hp3 : p ≤ 3
  · exact ballSincIntegral_lt_of_two_lt_le_three
      ballSincIntegral_three_le_seven_ninths p hp hp3
  · by_cases hp4 : p ≤ 4
    · exact ballSincIntegral_lt_of_three_le_le_four p (le_of_lt (lt_of_not_ge hp3)) hp4
    · exact ballSincIntegral_lt_sharp_of_four_le p (le_of_lt (lt_of_not_ge hp4))

/-- Integrability, sharp inequality, and the exact equality exponent p=2. -/
theorem strictBallSincBound : StrictBallSincBound :=
  strictBallSincBound_of_interior ballSincStrictInterior

/-- The full classical cube-section upper bound, including zero original rows
and the boundary ambient dimensions n=k and n=2k. -/
theorem classical_codimension_bound
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k :=
  classical_codimension_bound_of_ball strictBallSincBound n k hk hkn hn U

/-- The unconditional signed balanced-block equality classification in the
classical codimension range. -/
theorem classical_equality_iff
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k) (U : Frame n k) :
    sectionVolume U = sharpValue n k ↔ IsBalancedSection U :=
  classical_equality_iff_of_ball strictBallSincBound hk hkn hn U

theorem maximalSection_classical
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k ∧
      (sectionVolume U = sharpValue n k ↔ IsBalancedSection U) :=
  maximalSection_classical_of_interior ballSincStrictInterior n k hk hkn hn U

#print axioms ballSincStrictInterior
#print axioms strictBallSincBound
#print axioms classical_codimension_bound
#print axioms classical_equality_iff
#print axioms maximalSection_classical
end CubeSections
