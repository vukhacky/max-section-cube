import CubeSections.Certificates.ActualGroupedComparison
import CubeSections.Integer.ReciprocalWindow

/-! Interior small-quotient window closure. The original volume-ratio maximality
produces the reciprocal window and actual maximality. Only density and global
incidence remain analytical/geometric inputs.
-/
noncomputable section
open scoped BigOperators

namespace CubeSections.Certificates

theorem balanced_and_target_of_ratioMaximizing_smallQuotient {n k : ℕ}
    (q : ℕ) (hq : q=2 ∨ q=3 ∨ q=4) (hk : 1 ≤ k) (U : Frame n k)
    (hlo : q*k < n) (hhi : n < (q+1)*k)
    (hmax : RatioMaximalOnWindow q U) (hdensity : ActualClassDensity U q)
    (hincidence : (1/2 : ℝ) * ∑ c : RowClass U, ∑ d : RowClass U,
      classWeight U c d * pairAngularCost (rowClassMass U c) (rowClassMass U d)
        (rowClassAngle U c d) ≤ slabDeficit U) :
    IsBalancedSection U ∧ sectionVolume U = sharpValue n k := by
  have hq₂ : 2 ≤ q := by rcases hq with rfl | rfl | rfl <;> omega
  have hkn : k ≤ n := by nlinarith
  have hqn : n/k = q := by
    have hl : q ≤ n/k := (Nat.le_div_iff_mul_le (by omega)).mpr hlo.le
    have hh : n/k < q+1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hhi
    omega
  have hU : IsMaximizingFrame U := by
    intro V
    exact (div_le_div_iff_of_pos_right (sharpValue_pos hk hkn)).mp (hmax n hlo.le hhi.le V)
  have hwin := reciprocalWindow_of_ratio_maximal q hq₂ hk U hlo hhi hmax
  have hbalanced : IsBalancedSection U := by
    apply isBalancedSection_of_maximizing_smallQuotient hk hkn
      (by simpa only [hqn] using hq) U hU
    · simpa only [hqn] using hwin
    · simpa only [hqn] using hdensity
    · exact hincidence
  exact ⟨hbalanced,sectionVolume_eq_sharp_of_isBalancedSection U hbalanced⟩

theorem ratio_eq_one_of_ratioMaximizing_smallQuotient {n k : ℕ}
    (q : ℕ) (hq : q=2 ∨ q=3 ∨ q=4) (hk : 1 ≤ k) (U : Frame n k)
    (hlo : q*k < n) (hhi : n < (q+1)*k)
    (hmax : RatioMaximalOnWindow q U) (hdensity : ActualClassDensity U q)
    (hincidence : (1/2 : ℝ) * ∑ c : RowClass U, ∑ d : RowClass U,
      classWeight U c d * pairAngularCost (rowClassMass U c) (rowClassMass U d)
        (rowClassAngle U c d) ≤ slabDeficit U) :
    sectionVolume U / sharpValue n k = 1 := by
  have h := (balanced_and_target_of_ratioMaximizing_smallQuotient q hq hk U hlo hhi
    hmax hdensity hincidence).2
  rw [← h,div_self (ne_of_gt (sectionVolume_pos U))]

#print axioms balanced_and_target_of_ratioMaximizing_smallQuotient
#print axioms ratio_eq_one_of_ratioMaximizing_smallQuotient
end CubeSections.Certificates
