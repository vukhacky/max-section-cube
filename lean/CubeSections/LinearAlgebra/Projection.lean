import CubeSections.LinearAlgebra.Gram
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Entrywise bounds for Gram projections and their complementary projections. -/

noncomputable section
open Finset
open scoped Matrix

namespace CubeSections

theorem symmetricProjection_row_mul_sum {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hPs : P.transpose = P) (hPp : P * P = P) (i j : Fin n) :
    ∑ l, P i l * P j l = P i j := by
  have hsym (a b : Fin n) : P a b = P b a :=
    congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M b a) hPs
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hPp
  simpa only [Matrix.mul_apply, ← hsym j] using h

theorem symmetricProjection_row_sq_sum {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hPs : P.transpose = P) (hPp : P * P = P) (i : Fin n) :
    ∑ l, (P i l) ^ 2 = P i i := by
  simpa only [pow_two] using symmetricProjection_row_mul_sum P hPs hPp i i

/-- Every principal two-by-two minor of a real orthogonal projection is nonnegative. -/
theorem symmetricProjection_entry_sq_le {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hPs : P.transpose = P) (hPp : P * P = P) (i j : Fin n) :
    (P i j) ^ 2 ≤ P i i * P j j := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => P i l) (fun l => P j l)
  rw [symmetricProjection_row_mul_sum P hPs hPp i j,
    symmetricProjection_row_sq_sum P hPs hPp i,
    symmetricProjection_row_sq_sum P hPs hPp j] at h
  exact h

theorem complementProjection_transpose {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hPs : P.transpose = P) : (1 - P).transpose = 1 - P := by
  simp [Matrix.transpose_sub, hPs]

theorem complementProjection_mul_self {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hPp : P * P = P) : (1 - P) * (1 - P) = 1 - P := by
  simp [mul_sub, sub_mul, hPp]

/-- The complementary principal minor, including zero leverage and unit leverage endpoints. -/
theorem symmetricProjection_complement_entry_sq_le {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (hPs : P.transpose = P) (hPp : P * P = P)
    (i j : Fin n) (hij : i ≠ j) :
    (P i j) ^ 2 ≤ (1 - P i i) * (1 - P j j) := by
  have h := symmetricProjection_entry_sq_le (1 - P)
    (complementProjection_transpose P hPs) (complementProjection_mul_self P hPp) i j
  simpa [Matrix.sub_apply, Matrix.one_apply, hij] using h

theorem gramProjection_entry_sq_le {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    (gramProjection U i j) ^ 2 ≤ leverage U i * leverage U j :=
  symmetricProjection_entry_sq_le _ (gramProjection_transpose U)
    (gramProjection_mul_self U) i j

theorem gramProjection_complement_entry_sq_le {n k : ℕ}
    (U : Frame n k) (i j : Fin n) (hij : i ≠ j) :
    (gramProjection U i j) ^ 2 ≤ (1 - leverage U i) * (1 - leverage U j) :=
  symmetricProjection_complement_entry_sq_le _ (gramProjection_transpose U)
    (gramProjection_mul_self U) i j hij

theorem unit_leverage_offdiag_zero {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hi : leverage U i = 1) (hij : i ≠ j) : gramProjection U i j = 0 := by
  have h := gramProjection_complement_entry_sq_le U i j hij
  rw [hi] at h
  nlinarith [sq_nonneg (gramProjection U i j)]

theorem zero_leverage_row_zero {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hi : leverage U i = 0) : gramProjection U i j = 0 := by
  have h := gramProjection_entry_sq_le U i j
  rw [hi] at h
  nlinarith [sq_nonneg (gramProjection U i j)]

end CubeSections
