import CubeSections.Integer.EntropyGap

/-!
# Volume comparison from an explicitly assumed angular inequality

These are conditional reductions on an actual cube-section frame. The global
angular inequality and the applicability of the reciprocal window are not
assumed to have been proved for arbitrary frames.
-/
noncomputable section
open scoped BigOperators
namespace CubeSections

/-- Exact direct criterion, retaining both nonnegative packing remainders. -/
theorem log_target_ratio_ge_angular_remainders {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (U : Frame n k)
    (hwin : ReciprocalWindow (n / k) U) (C : ℝ)
    (hangular : gramAngularDefect U ≤ C * slabDeficit U) :
    (1 - C * sharpEntropyCoeff (n / k) / 2) * slabDeficit U +
      sharpEntropyCoeff (n / k) / 2 *
        (gramPackingRemainder (n / k) U + gramMismatchRemainder U) ≤
      Real.log (sharpValue n k / sectionVolume U) := by
  have hq := quotient_pos hk hkn
  have hA := sharpEntropyCoeff_pos (n / k) hq
  have hent := sum_entropyExcess_le (n / k) hq U hwin
  have hmul := mul_le_mul_of_nonneg_left hangular hA.le
  rw [gramPacking_identity (n / k) U] at hmul
  rw [log_target_ratio hk hkn U hwin]
  nlinarith

/-- A positive angular constant forces a nonnegative actual slab deficit. -/
theorem slabDeficit_nonneg_of_angular {n k : ℕ}
    (q : ℕ) (hq : 1 ≤ q) (U : Frame n k)
    (hrep : RowReplacement U) (hwin : ReciprocalWindow q U)
    (C : ℝ) (hC : 0 < C)
    (hangular : gramAngularDefect U ≤ C * slabDeficit U) :
    0 ≤ slabDeficit U := by
  have hE := (integerDefect_nonneg q hq U hwin).trans
    (gramAngularDefect_ge_integerDefect q hq U hrep hwin)
  exact nonneg_of_mul_nonneg_left (by simpa only [mul_comm] using hE.trans hangular) hC

/-- A conditional volume bound from the angular comparison, on the exact frame. -/
theorem sectionVolume_le_sharp_of_angular {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (U : Frame n k)
    (hrep : RowReplacement U) (hwin : ReciprocalWindow (n / k) U)
    (C : ℝ) (hC : 0 < C) (hcoef : C * sharpEntropyCoeff (n / k) / 2 < 1)
    (hangular : gramAngularDefect U ≤ C * slabDeficit U) :
    sectionVolume U ≤ sharpValue n k := by
  have hq := quotient_pos hk hkn
  have hδ := slabDeficit_nonneg_of_angular (n / k) hq U hrep hwin C hC hangular
  have hA := sharpEntropyCoeff_pos (n / k) hq
  have hP := gramPackingRemainder_nonneg (n / k) hq U hrep hwin
  have hH := gramMismatchRemainder_nonneg U
  have hmain := log_target_ratio_ge_angular_remainders hk hkn U hwin C hangular
  have hlog : 0 ≤ Real.log (sharpValue n k / sectionVolume U) := by
    exact (add_nonneg (mul_nonneg (sub_nonneg.mpr hcoef.le) hδ)
      (mul_nonneg (by positivity) (add_nonneg hP hH))).trans hmain
  have hratio : 1 ≤ sharpValue n k / sectionVolume U :=
    (Real.log_nonneg_iff (div_pos (sharpValue_pos hk hkn) (sectionVolume_pos U))).mp hlog
  exact (one_le_div (sectionVolume_pos U)).mp hratio

theorem sectionVolume_lt_sharp_of_angular_of_deficit_pos {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (U : Frame n k)
    (hrep : RowReplacement U) (hwin : ReciprocalWindow (n / k) U)
    (C : ℝ) (hcoef : C * sharpEntropyCoeff (n / k) / 2 < 1)
    (hangular : gramAngularDefect U ≤ C * slabDeficit U)
    (hδ : 0 < slabDeficit U) :
    sectionVolume U < sharpValue n k := by
  have hq := quotient_pos hk hkn
  have hA := sharpEntropyCoeff_pos (n / k) hq
  have hP := gramPackingRemainder_nonneg (n / k) hq U hrep hwin
  have hH := gramMismatchRemainder_nonneg U
  have hmain := log_target_ratio_ge_angular_remainders hk hkn U hwin C hangular
  have hlog : 0 < Real.log (sharpValue n k / sectionVolume U) := by
    exact (add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hcoef) hδ)
      (mul_nonneg (by positivity) (add_nonneg hP hH))).trans_le hmain
  have hratio : 1 < sharpValue n k / sectionVolume U :=
    (Real.log_pos_iff (div_nonneg (sharpValue_nonneg _ _) (sectionVolume_pos U).le)).mp hlog
  exact (one_lt_div (sectionVolume_pos U)).mp hratio

/-- The coefficient remains strictly positive at q=5. -/
theorem largeQuotient_coefficient_pos (q : ℕ) (hq : 5 ≤ q) :
    0 < 1 - 10 * sharpEntropyCoeff q := by
  have hq₁ : 1 ≤ q := by omega
  have hqR : (5 : ℝ) ≤ q := by exact_mod_cast hq
  have hA := sharpEntropyCoeff_lt q hq₁
  have hb : (1 : ℝ) / (2 * (q : ℝ)) ≤ 1 / 10 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have hlt := hA.trans_le hb
  linarith

/-- The large-quotient comparison, conditional only on the stated geometric/analytic inputs. -/
theorem sectionVolume_le_sharp_largeQuotient {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hq : 5 ≤ n / k) (U : Frame n k)
    (hrep : RowReplacement U) (hwin : ReciprocalWindow (n / k) U)
    (hangular : gramAngularDefect U ≤ 20 * slabDeficit U) :
    sectionVolume U ≤ sharpValue n k := by
  apply sectionVolume_le_sharp_of_angular hk hkn U hrep hwin 20 (by norm_num)
  · have h := largeQuotient_coefficient_pos (n / k) hq
    linarith
  · exact hangular

/-- Equality in the conditional large-quotient comparison forces zero angular defect. -/
theorem angularDefect_zero_of_largeQuotient_equality {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hq : 5 ≤ n / k) (U : Frame n k)
    (hrep : RowReplacement U) (hwin : ReciprocalWindow (n / k) U)
    (hangular : gramAngularDefect U ≤ 20 * slabDeficit U)
    (heq : sectionVolume U = sharpValue n k) :
    gramAngularDefect U = 0 := by
  have hδ := slabDeficit_nonneg_of_angular (n / k) (quotient_pos hk hkn) U hrep hwin
    20 (by norm_num) hangular
  have hδzero : slabDeficit U = 0 := by
    by_contra hne
    have hδpos : 0 < slabDeficit U := lt_of_le_of_ne hδ (Ne.symm hne)
    have hlt := sectionVolume_lt_sharp_of_angular_of_deficit_pos hk hkn U hrep hwin
      20 (by have h := largeQuotient_coefficient_pos (n / k) hq; linarith) hangular hδpos
    exact (ne_of_lt hlt) heq
  have hE := (integerDefect_nonneg (n / k) (quotient_pos hk hkn) U hwin).trans
    (gramAngularDefect_ge_integerDefect (n / k) (quotient_pos hk hkn) U hrep hwin)
  rw [hδzero, mul_zero] at hangular
  exact le_antisymm hangular hE

end CubeSections
