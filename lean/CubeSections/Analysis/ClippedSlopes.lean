import CubeSections.Analysis.ClippedPaths

/-! Exact matrix trace expressions for the two clipped derivatives. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder

namespace CubeSections

theorem cutoffMatrix_eq_smul {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) (t : ℝ) :
    cutoffMatrix U z t = Real.exp (-t) •
      weightedGram (frameMatrix U) (fun i => Real.exp (clippedPotential z t i)) := by
  calc
    _ = weightedGram (frameMatrix U)
        (fun i => Real.exp (-t) * Real.exp (clippedPotential z t i)) := by
      unfold cutoffMatrix
      congr 1
      funext i
      rw [← Real.exp_add]
      congr 1
      ring
    _ = _ := weightedGram_const_mul _ _ _

theorem cutoffMatrix_inv {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) (t : ℝ) :
    (cutoffMatrix U z t)⁻¹ = Real.exp t •
      (weightedGram (frameMatrix U) (fun i => Real.exp (clippedPotential z t i)))⁻¹ := by
  let M := weightedGram (frameMatrix U) (fun i => Real.exp (clippedPotential z t i))
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr
    (ne_of_gt (det_weightedGram_exp_pos U (clippedPotential z t)))
  apply Matrix.inv_eq_left_inv
  rw [cutoffMatrix_eq_smul]
  change (Real.exp t • M⁻¹) * (Real.exp (-t) • M) = 1
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul M hM,
    smul_smul, ← Real.exp_add, add_neg_cancel, neg_add_cancel, Real.exp_zero, one_smul]

theorem hasDerivAt_clipped_determinantRemainder {n k : ℕ} (U : Frame n k)
    (z : Fin n → ℝ) (t : ℝ) (hz : ∀ i, z i ≠ t) :
    HasDerivAt (fun s => determinantRemainder U (clippedPotential z s))
      (Matrix.trace (cutoffActiveMatrix U z t * ((cutoffMatrix U z t)⁻¹ - 1))) t := by
  have h := hasDerivAt_determinantRemainder U (clippedPotential z) (cutoffActivity z t) t
    (fun i => hasDerivAt_clippedPotential z t i (hz i))
  convert h using 1
  rw [cutoffActiveMatrix, trace_weightedGram_mul, cutoffMatrix_inv]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    Matrix.smul_mulVec, dotProduct_smul, frameRow_dot_self]
  by_cases hact : t < z i
  · simp [cutoffActivity, clippedPotential, hact, min_eq_right hact.le]
  · simp [cutoffActivity, hact]

theorem trace_cutoffActive_one_sub {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) (t : ℝ) :
    Matrix.trace (cutoffActiveMatrix U z t * (1 - cutoffMatrix U z t)) =
      ∑ i, ∑ j, cutoffActivity z t i *
        (1 - Real.exp (clippedPotential z t j - t)) * gramProjection U i j ^ 2 := by
  unfold cutoffActiveMatrix cutoffMatrix
  rw [← frame_weightedGram_one U, ← weightedGram_sub, trace_weightedGram_mul_weightedGram]

theorem clippedPairSlope_sum_eq_trace {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) (t : ℝ) :
    (1 / 2 : ℝ) * ∑ i, ∑ j, gramProjection U i j ^ 2 * clippedPairSlope (z i) (z j) t =
      Matrix.trace (cutoffActiveMatrix U z t * (1 - cutoffMatrix U z t)) := by
  rw [trace_cutoffActive_one_sub]
  let f : Fin n → Fin n → ℝ := fun i j => cutoffActivity z t i *
    (1 - Real.exp (clippedPotential z t j - t)) * gramProjection U i j ^ 2
  have hpair (i j : Fin n) :
      gramProjection U i j ^ 2 * clippedPairSlope (z i) (z j) t = f i j + f j i := by
    dsimp [f, cutoffActivity, clippedPotential, clippedPairSlope]
    rw [gramProjection_symm U j i]
    ring
  change (1 / 2 : ℝ) * ∑ i, ∑ j, gramProjection U i j ^ 2 * clippedPairSlope (z i) (z j) t =
    ∑ i, ∑ j, f i j
  simp only [hpair, Finset.sum_add_distrib]
  have hcomm : (∑ i, ∑ j, f j i) = ∑ i, ∑ j, f i j := Finset.sum_comm
  rw [hcomm]
  ring

theorem hasDerivAt_clipped_gramPairProduction {n k : ℕ} (U : Frame n k)
    (z : Fin n → ℝ) (t : ℝ) (hz : ∀ i, z i ≠ t) :
    HasDerivAt (fun s => gramPairProduction U (clippedPotential z s))
      (Matrix.trace (cutoffActiveMatrix U z t * (1 - cutoffMatrix U z t))) t := by
  have h := hasDerivAt_gramPairProduction_clipped U z t hz
  rwa [clippedPairSlope_sum_eq_trace] at h

theorem hasDerivAt_clipped_remainder_difference {n k : ℕ} (U : Frame n k)
    (z : Fin n → ℝ) (t : ℝ) (hz : ∀ i, z i ≠ t) :
    HasDerivAt
      (fun s => determinantRemainder U (clippedPotential z s) -
        gramPairProduction U (clippedPotential z s))
      (Matrix.trace (cutoffActiveMatrix U z t * ((cutoffMatrix U z t)⁻¹ - 1)) -
        Matrix.trace (cutoffActiveMatrix U z t * (1 - cutoffMatrix U z t))) t :=
  (hasDerivAt_clipped_determinantRemainder U z t hz).sub
    (hasDerivAt_clipped_gramPairProduction U z t hz)

theorem clipped_remainder_slope_nonneg {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) (t : ℝ) :
    0 ≤ Matrix.trace (cutoffActiveMatrix U z t * ((cutoffMatrix U z t)⁻¹ - 1)) -
      Matrix.trace (cutoffActiveMatrix U z t * (1 - cutoffMatrix U z t)) :=
  sub_nonneg.mpr (clipped_trace_comparison _ _
    (cutoffActiveMatrix_posSemidef U z t) (cutoffMatrix_posDef U z t))

end CubeSections
