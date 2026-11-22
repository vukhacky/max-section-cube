import CubeSections.Geometry.Variational

/-!
# Actual two-row strip competitors

This module constructs the raw linear map, proves the one-sided slab inclusion,
and computes its determinant. The retained-volume estimate is an explicit input;
no density or coarea assertion is supplied by these algebraic comparisons.
-/

noncomputable section
open Set MeasureTheory Finset
open scoped Matrix ENNReal

namespace CubeSections

def mergeRowsMap {n k : ℕ} (U : Frame n k) (i j : Fin n) (t : ℝ) : E k →ₗ[ℝ] E n where
  toFun x := WithLp.toLp 2 (fun p =>
    if p = i ∨ p = j then ((U x) i + (U x) j) / (2 * (1 - t)) else (U x) p)
  map_add' x y := by
    ext p
    by_cases hp : p = i ∨ p = j
    · simp [hp, add_div] <;> ring
    · simp [hp]
  map_smul' c x := by
    ext p
    by_cases hp : p = i ∨ p = j
    · simp [hp, mul_add] <;> ring
    · simp [hp]

@[simp] theorem mergeRowsMap_apply {n k : ℕ} (U : Frame n k) (i j p : Fin n)
    (t : ℝ) (x : E k) :
    (mergeRowsMap U i j t x) p =
      if p = i ∨ p = j then ((U x) i + (U x) j) / (2 * (1 - t)) else (U x) p := rfl

def mergedRow {n k : ℕ} (U : Frame n k) (i j : Fin n) (t : ℝ) : Fin k → ℝ :=
  fun a => (frameMatrix U i a + frameMatrix U j a) / (2 * (1 - t))

theorem rawMatrix_mergeRowsMap {n k : ℕ} (U : Frame n k) (i j : Fin n) (t : ℝ) :
    rawMatrix (mergeRowsMap U i j t) =
      ((frameMatrix U).updateRow i (mergedRow U i j t)).updateRow j (mergedRow U i j t) := by
  ext p a
  by_cases hpi : p = i <;> by_cases hpj : p = j <;>
    simp [rawMatrix, frameMatrix, mergedRow, Matrix.updateRow_apply, hpi, hpj]

theorem mergeRowsMap_gram_update {n k : ℕ} (U : Frame n k)
    (i j : Fin n) (hij : i ≠ j) (t : ℝ) :
    (rawMatrix (mergeRowsMap U i j t)).transpose * rawMatrix (mergeRowsMap U i j t) =
      1 - Matrix.vecMulVec (frameMatrix U i) (frameMatrix U i) +
        Matrix.vecMulVec (mergedRow U i j t) (mergedRow U i j t) -
        Matrix.vecMulVec (frameMatrix U j) (frameMatrix U j) +
        Matrix.vecMulVec (mergedRow U i j t) (mergedRow U i j t) := by
  rw [rawMatrix_mergeRowsMap, transpose_mul_updateRow, transpose_mul_updateRow,
    frameMatrix_transpose_mul]
  have hrow : ((frameMatrix U).updateRow i (mergedRow U i j t)) j = frameMatrix U j := by
    funext a
    simp [Matrix.updateRow_apply, Ne.symm hij]
  rw [hrow]

theorem mergeRowsMap_gram {n k : ℕ} (U : Frame n k)
    (i j : Fin n) (hij : i ≠ j) (t : ℝ) (ht : t < 1) :
    (rawMatrix (mergeRowsMap U i j t)).transpose * rawMatrix (mergeRowsMap U i j t) =
      1 - (1 / 2 : ℝ) • Matrix.vecMulVec (frameMatrix U i - frameMatrix U j)
        (frameMatrix U i - frameMatrix U j) +
        ((1 / (1 - t) ^ 2 - 1) / 2) •
          Matrix.vecMulVec (frameMatrix U i + frameMatrix U j)
            (frameMatrix U i + frameMatrix U j) := by
  rw [mergeRowsMap_gram_update U i j hij]
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.add_apply, Pi.sub_apply, smul_eq_mul, mergedRow]
  field_simp [ne_of_gt (sub_pos.mpr ht)] <;> ring

theorem mergeRowsMap_det {n k : ℕ} (U : Frame n k)
    (i j : Fin n) (hij : i ≠ j) (t : ℝ) (ht : t < 1) :
    Matrix.det ((rawMatrix (mergeRowsMap U i j t)).transpose *
      rawMatrix (mergeRowsMap U i j t)) =
      1 - (leverage U i + leverage U j) / 2 + gramProjection U i j +
        (1 / (1 - t) ^ 2 - 1) *
          ((leverage U i + leverage U j) / 2 + gramProjection U i j -
            leverage U i * leverage U j + gramProjection U i j ^ 2) := by
  rw [mergeRowsMap_gram U i j hij t ht, det_two_row_merge,
    frameRow_dot_self, frameRow_dot_self, frameRow_dot]

theorem mergeRowsMap_det_pos {n k : ℕ} (U : Frame n k)
    (i j : Fin n) (hij : i ≠ j) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hi : leverage U i ≤ 1 / 2) (hj : leverage U j ≤ 1 / 2)
    (hP : 0 ≤ gramProjection U i j) :
    0 < Matrix.det ((rawMatrix (mergeRowsMap U i j t)).transpose *
      rawMatrix (mergeRowsMap U i j t)) := by
  rw [mergeRowsMap_det U i j hij t (by linarith)]
  have hc := leverage_nonneg U i
  have hd := leverage_nonneg U j
  have hL : 0 ≤ (leverage U i + leverage U j) / 2 + gramProjection U i j -
      leverage U i * leverage U j + gramProjection U i j ^ 2 := by
    have hprod := mul_nonneg hc (show 0 ≤ (1 / 2 : ℝ) - leverage U j by linarith)
    nlinarith [sq_nonneg (gramProjection U i j)]
  have ha : 0 < 1 - t := by linarith
  have hsq : 0 < (1 - t) ^ 2 := sq_pos_of_pos ha
  have hcoeff : 0 ≤ 1 / (1 - t) ^ 2 - 1 := by
    apply sub_nonneg.mpr
    apply (le_div_iff₀ hsq).mpr
    nlinarith [mul_nonneg ht0 (show 0 ≤ 2 - t by linarith)]
  nlinarith [mul_nonneg hcoeff hL]

theorem mergeRowsMap_injective {n k : ℕ} (U : Frame n k)
    (i j : Fin n) (hij : i ≠ j) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hi : leverage U i ≤ 1 / 2) (hj : leverage U j ≤ 1 / 2)
    (hP : 0 ≤ gramProjection U i j) : Function.Injective (mergeRowsMap U i j t) :=
  injective_of_rawMatrix_det_pos _ (mergeRowsMap_det_pos U i j hij t ht0 ht1 hi hj hP)

def twoRowStrip {n k : ℕ} (U : Frame n k) (i j : Fin n) (t : ℝ) : Set (E k) :=
  {x | |(U x) i + (U x) j| ≤ 1 - t}

theorem section_inter_strip_subset_mergeRowsMap_slab {n k : ℕ} (U : Frame n k)
    (i j : Fin n) (t : ℝ) (ht : t < 1) :
    (U ⁻¹' cube n) ∩ twoRowStrip U i j t ⊆ rawSlab (mergeRowsMap U i j t) := by
  rintro x ⟨hx, hs⟩ p
  rw [mergeRowsMap_apply]
  split_ifs with hp
  · have hden : 0 < 2 * (1 - t) := mul_pos (by norm_num) (sub_pos.mpr ht)
    rw [abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).mpr
    change |(U x) i + (U x) j| ≤ 1 - t at hs
    linarith
  · exact hx p

theorem maximizing_det_mul_retained_sq_le {n k : ℕ} (U : Frame n k)
    (hU : IsMaximizingFrame U) (R : E k →ₗ[ℝ] E n) (hR : Function.Injective R)
    (a : ℝ) (ha : 0 ≤ a) (hretained : a * sectionVolume U ≤ rawVolume R) :
    Matrix.det ((rawMatrix R).transpose * rawMatrix R) * a ^ 2 ≤ 1 := by
  have hnorm : R.normDet * (a * sectionVolume U) ≤ sectionVolume U := by
    calc
      _ ≤ R.normDet * rawVolume R :=
        mul_le_mul_of_nonneg_left hretained R.normDet_nonneg
      _ = sectionVolume (normalizedFrame R hR) :=
        (sectionVolume_eq_normDet_mul_rawVolume R (normalizedFrame R hR)
          (normalizedFrame_range R hR)).symm
      _ ≤ sectionVolume U := hU _
  have hprod : R.normDet * a ≤ 1 := by
    apply (mul_le_mul_iff_left₀ (sectionVolume_pos U)).mp
    simpa only [mul_assoc, one_mul] using hnorm
  have hnonneg : 0 ≤ R.normDet * a := mul_nonneg R.normDet_nonneg ha
  have hs := mul_nonneg (sub_nonneg.mpr hprod) (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hnonneg)
  rw [← normDet_sq_eq_det_rawMatrix]
  nlinarith

theorem maximizing_mergeRows_det_mul_retained_sq_le {n k : ℕ} (U : Frame n k)
    (hU : IsMaximizingFrame U) (i j : Fin n) (hij : i ≠ j)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hi : leverage U i ≤ 1 / 2) (hj : leverage U j ≤ 1 / 2)
    (hP : 0 ≤ gramProjection U i j) (a : ℝ) (ha : 0 ≤ a)
    (hretained : a * sectionVolume U ≤
      (volume ((U ⁻¹' cube n) ∩ twoRowStrip U i j t)).toReal) :
    (1 - (leverage U i + leverage U j) / 2 + gramProjection U i j +
      (1 / (1 - t) ^ 2 - 1) *
        ((leverage U i + leverage U j) / 2 + gramProjection U i j -
          leverage U i * leverage U j + gramProjection U i j ^ 2)) * a ^ 2 ≤ 1 := by
  have ht : t < 1 := by linarith
  have hR := mergeRowsMap_injective U i j hij t ht0 ht1 hi hj hP
  have hraw : a * sectionVolume U ≤ rawVolume (mergeRowsMap U i j t) := by
    apply hretained.trans
    exact ENNReal.toReal_mono (rawMass_ne_top _ hR)
      (measure_mono (section_inter_strip_subset_mergeRowsMap_slab U i j t ht))
  have h := maximizing_det_mul_retained_sq_le U hU (mergeRowsMap U i j t) hR a ha hraw
  rwa [mergeRowsMap_det U i j hij t ht] at h

end CubeSections
