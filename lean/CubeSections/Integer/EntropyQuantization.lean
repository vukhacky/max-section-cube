import CubeSections.Integer.EntropyGap

/-! Nonnegative entropy gap and its exact relation to the continuous slab factor. -/
noncomputable section
open scoped BigOperators
namespace CubeSections

/-- Continuous slab factor, including the entropy convention for zero rows. -/
def slabBound {n k : ℕ} (U : Frame n k) : ℝ := Real.exp (slabLogBound U)

theorem slabBound_pos {n k : ℕ} (U : Frame n k) : 0 < slabBound U := Real.exp_pos _

theorem slabDeficit_eq_log_ratio {n k : ℕ} (U : Frame n k) :
    slabDeficit U = Real.log (slabBound U / sectionVolume U) := by
  rw [Real.log_div (ne_of_gt (slabBound_pos U)) (ne_of_gt (sectionVolume_pos U))]
  rw [slabBound, Real.log_exp]
  rfl

theorem sum_entropyExcess_nonneg {n k : ℕ} (q : ℕ) (hq : 1 ≤ q) (U : Frame n k)
    (hwin : ReciprocalWindow q U) :
    0 ≤ ∑ i : Fin n, entropyExcess q (leverage U i) := by
  exact Finset.sum_nonneg (fun i _ => entropyExcess_nonneg q hq _ (hwin i).1 (hwin i).2)

theorem log_slabBound_target_eq {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (U : Frame n k)
    (hwin : ReciprocalWindow (n / k) U) :
    Real.log (slabBound U / sharpValue n k) =
      (∑ i : Fin n, entropyExcess (n / k) (leverage U i)) / 2 := by
  rw [Real.log_div (ne_of_gt (slabBound_pos U)) (ne_of_gt (sharpValue_pos hk hkn)),
    slabBound, Real.log_exp, sum_entropyExcess_eq hk hkn U hwin]
  ring

/-- Both bounds in the manuscript's integer entropy quantization inequality. -/
theorem integer_entropy_quantization {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (U : Frame n k) (hwin : ReciprocalWindow (n / k) U) :
    0 ≤ Real.log (slabBound U / sharpValue n k) ∧
      Real.log (slabBound U / sharpValue n k) ≤
        sharpEntropyCoeff (n / k) / 2 * integerDefect (n / k) U := by
  rw [log_slabBound_target_eq hk hkn U hwin]
  have hlo := sum_entropyExcess_nonneg (n / k) (quotient_pos hk hkn) U hwin
  have hup := sum_entropyExcess_le (n / k) (quotient_pos hk hkn) U hwin
  constructor <;> linarith

theorem integer_entropy_quantization_strict {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (U : Frame n k) (hwin : ReciprocalWindow (n / k) U)
    (hint : ∃ i : Fin n, 1 / (((n / k : ℕ) : ℝ) + 1) < leverage U i ∧
      leverage U i < 1 / ((n / k : ℕ) : ℝ)) :
    Real.log (slabBound U / sharpValue n k) <
      sharpEntropyCoeff (n / k) / 2 * integerDefect (n / k) U := by
  rw [log_slabBound_target_eq hk hkn U hwin]
  have h := sum_entropyExcess_lt_of_interior (n / k) (quotient_pos hk hkn) U hwin hint
  linarith

end CubeSections
