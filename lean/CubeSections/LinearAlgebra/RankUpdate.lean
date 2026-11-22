import CubeSections.LinearAlgebra.Gram
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Ring

/-! Exact determinant identities for one- and two-row modifications. -/

noncomputable section
open scoped Matrix
open Finset

namespace CubeSections

theorem det_one_add_outer {k : ℕ} (u v : Fin k → ℝ) :
    Matrix.det (1 + Matrix.vecMulVec u v) = 1 + v ⬝ᵥ u := by
  rw [Matrix.vecMulVec_eq Unit]
  exact Matrix.det_one_add_replicateCol_mul_replicateRow u v

theorem det_one_add_scaled_outer {k : ℕ} (v : Fin k → ℝ) (a : ℝ) :
    Matrix.det (1 + a • Matrix.vecMulVec v v) = 1 + a * (v ⬝ᵥ v) := by
  rw [← Matrix.smul_vecMulVec, det_one_add_outer]
  simp [dotProduct, Finset.mul_sum, mul_left_comm]

/-- The two-by-two determinant reduction has no nondegeneracy requirement. -/
theorem det_one_add_two_scaled_outer {k : ℕ} (v w : Fin k → ℝ) (a b : ℝ) :
    Matrix.det (1 + a • Matrix.vecMulVec v v + b • Matrix.vecMulVec w w) =
      (1 + a * (v ⬝ᵥ v)) * (1 + b * (w ⬝ᵥ w)) - a * b * (v ⬝ᵥ w) ^ 2 := by
  let A : Matrix (Fin k) (Fin 2) ℝ := fun i j => ![a * v i, b * w i] j
  let B : Matrix (Fin 2) (Fin k) ℝ := ![v, w]
  have hAB : A * B = a • Matrix.vecMulVec v v + b • Matrix.vecMulVec w w := by
    ext i j
    rw [Matrix.mul_apply]
    simp [A, B, Fin.sum_univ_two, Matrix.vecMulVec_apply,
      mul_assoc]
  have hform : 1 + a • Matrix.vecMulVec v v + b • Matrix.vecMulVec w w = 1 + A * B := by
    rw [hAB]
    exact add_assoc _ _ _
  have h00 : (B * A) 0 0 = a * (v ⬝ᵥ v) := by
    rw [Matrix.mul_apply]
    simp [A, B, dotProduct, Finset.mul_sum, mul_left_comm]
  have h01 : (B * A) 0 1 = b * (v ⬝ᵥ w) := by
    rw [Matrix.mul_apply]
    simp [A, B, dotProduct, Finset.mul_sum, mul_left_comm]
  have h10 : (B * A) 1 0 = a * (v ⬝ᵥ w) := by
    rw [Matrix.mul_apply]
    simp [A, B, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
  have h11 : (B * A) 1 1 = b * (w ⬝ᵥ w) := by
    rw [Matrix.mul_apply]
    simp [A, B, dotProduct, Finset.mul_sum, mul_left_comm]
  rw [hform, Matrix.det_one_add_mul_comm, Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.one_apply, h00, h01, h10, h11]
  norm_num
  ring

/-- Determinant of the sum/difference two-row modification, without square-root coordinates. -/
theorem det_two_row_merge {k : ℕ} (v w : Fin k → ℝ) (coeff : ℝ) :
    Matrix.det (1 - (1 / 2 : ℝ) • Matrix.vecMulVec (v - w) (v - w) +
      (coeff / 2) • Matrix.vecMulVec (v + w) (v + w)) =
      1 - ((v ⬝ᵥ v) + (w ⬝ᵥ w)) / 2 + v ⬝ᵥ w +
        coeff * (((v ⬝ᵥ v) + (w ⬝ᵥ w)) / 2 + v ⬝ᵥ w -
          (v ⬝ᵥ v) * (w ⬝ᵥ w) + (v ⬝ᵥ w) ^ 2) := by
  have hm : (v - w) ⬝ᵥ (v - w) = (v ⬝ᵥ v) + (w ⬝ᵥ w) - 2 * (v ⬝ᵥ w) := by
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm w v]
    ring
  have hp : (v + w) ⬝ᵥ (v + w) = (v ⬝ᵥ v) + (w ⬝ᵥ w) + 2 * (v ⬝ᵥ w) := by
    simp only [add_dotProduct, dotProduct_add, dotProduct_comm w v]
    ring
  have hmp : (v - w) ⬝ᵥ (v + w) = (v ⬝ᵥ v) - (w ⬝ᵥ w) := by
    simp only [sub_dotProduct, dotProduct_add, dotProduct_comm w v]
    ring
  have h := det_one_add_two_scaled_outer (v - w) (v + w) (-(1 / 2 : ℝ)) (coeff / 2)
  simp only [neg_smul, hm, hp, hmp] at h
  rw [sub_eq_add_neg, h]
  ring

theorem frameRow_dot_self {n k : ℕ} (U : Frame n k) (i : Fin n) :
    frameMatrix U i ⬝ᵥ frameMatrix U i = leverage U i := by
  simp [leverage, gramProjection, Matrix.mul_apply, dotProduct]

theorem frameRow_dot {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    frameMatrix U i ⬝ᵥ frameMatrix U j = gramProjection U i j := by
  simp [gramProjection, Matrix.mul_apply, dotProduct]

theorem det_duplicate_row {n k : ℕ} (U : Frame n k) (i : Fin n) :
    Matrix.det (1 + Matrix.vecMulVec (frameMatrix U i) (frameMatrix U i)) =
      1 + leverage U i := by
  rw [det_one_add_outer, frameRow_dot_self]

theorem det_delete_row {n k : ℕ} (U : Frame n k) (i : Fin n) :
    Matrix.det (1 - Matrix.vecMulVec (frameMatrix U i) (frameMatrix U i)) =
      1 - leverage U i := by
  have h := det_one_add_scaled_outer (frameMatrix U i) (-1)
  simpa [frameRow_dot_self, sub_eq_add_neg] using h

theorem det_replace_row {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    Matrix.det (1 - Matrix.vecMulVec (frameMatrix U i) (frameMatrix U i) +
      Matrix.vecMulVec (frameMatrix U j) (frameMatrix U j)) =
      1 - leverage U i + leverage U j - leverage U i * leverage U j +
        (gramProjection U i j) ^ 2 := by
  have h := det_one_add_two_scaled_outer (frameMatrix U i) (frameMatrix U j) (-1) 1
  simp only [neg_smul, one_smul, frameRow_dot_self, frameRow_dot] at h
  rw [sub_eq_add_neg]
  rw [h]
  ring

theorem det_duplicate_row_pos {n k : ℕ} (U : Frame n k) (i : Fin n) :
    0 < Matrix.det (1 + Matrix.vecMulVec (frameMatrix U i) (frameMatrix U i)) := by
  rw [det_duplicate_row]
  linarith [leverage_nonneg U i]

theorem det_delete_row_pos {n k : ℕ} (U : Frame n k) (i : Fin n)
    (hi : leverage U i < 1) :
    0 < Matrix.det (1 - Matrix.vecMulVec (frameMatrix U i) (frameMatrix U i)) := by
  rw [det_delete_row]
  linarith

/-- Algebraic consequence of the two ordered row-replacement comparisons.
The volume-maximality argument supplying these determinant hypotheses is separate. -/
theorem leverage_gap_of_rowReplacement_det_le {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hij : Matrix.det (1 - Matrix.vecMulVec (frameMatrix U i) (frameMatrix U i) +
      Matrix.vecMulVec (frameMatrix U j) (frameMatrix U j)) ≤ 1)
    (hji : Matrix.det (1 - Matrix.vecMulVec (frameMatrix U j) (frameMatrix U j) +
      Matrix.vecMulVec (frameMatrix U i) (frameMatrix U i)) ≤ 1) :
    |leverage U i - leverage U j| ≤
      leverage U i * leverage U j - (gramProjection U i j) ^ 2 := by
  rw [det_replace_row] at hij hji
  rw [gramProjection_symm U j i] at hji
  apply abs_le.mpr
  constructor <;> nlinarith

end CubeSections
