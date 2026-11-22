import CubeSections.LinearAlgebra.Gram
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Ring

/-! The Gram-weighted variance is a contraction in the leverage-weighted norm. -/

noncomputable section
open scoped BigOperators Matrix

namespace CubeSections

/-- Ordered-pair form of the manuscript's unordered Gram variance. -/
def gramVariance {n k : ℕ} (U : Frame n k) (v : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, gramProjection U i j ^ 2 * (v i - v j) ^ 2

def gramSchurForm {n k : ℕ} (U : Frame n k) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, gramProjection U i j ^ 2 * v i * v j

theorem gramProjection_posSemidef {n k : ℕ} (U : Frame n k) :
    (gramProjection U).PosSemidef := by
  simpa [gramProjection] using Matrix.posSemidef_self_mul_conjTranspose (frameMatrix U)

theorem gramSchurForm_nonneg {n k : ℕ} (U : Frame n k) (v : Fin n → ℝ) :
    0 ≤ gramSchurForm U v := by
  have h := ((gramProjection_posSemidef U).hadamard (gramProjection_posSemidef U)).dotProduct_mulVec_nonneg v
  simpa [gramSchurForm, dotProduct, Matrix.mulVec, Matrix.hadamard_apply,
    Finset.mul_sum, pow_two, mul_assoc, mul_comm, mul_left_comm] using h

/-- Exact variance decomposition; the discarded term is a positive semidefinite Schur form. -/
theorem gramVariance_identity {n k : ℕ} (U : Frame n k) (v : Fin n → ℝ) :
    gramVariance U v = (∑ i, leverage U i * v i ^ 2) - gramSchurForm U v := by
  have hswap : (∑ i, ∑ j, gramProjection U i j ^ 2 * v j ^ 2) =
      ∑ i, ∑ j, gramProjection U i j ^ 2 * v i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [gramProjection_symm U j i]
  have hrow : (∑ i, ∑ j, gramProjection U i j ^ 2 * v i ^ 2) =
      ∑ i, leverage U i * v i ^ 2 := by
    simp_rw [← Finset.sum_mul, gramProjection_row_sq_sum]
  have hexp : (∑ i, ∑ j, gramProjection U i j ^ 2 * (v i - v j) ^ 2) =
      (∑ i, ∑ j, gramProjection U i j ^ 2 * v i ^ 2) +
      (∑ i, ∑ j, gramProjection U i j ^ 2 * v j ^ 2) -
      2 * gramSchurForm U v := by
    calc
      _ = ∑ i, ∑ j, (gramProjection U i j ^ 2 * v i ^ 2 +
          gramProjection U i j ^ 2 * v j ^ 2 -
          2 * (gramProjection U i j ^ 2 * v i * v j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        simp only [gramSchurForm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold gramVariance
  rw [hexp, hswap, hrow]
  ring

theorem gramVariance_nonneg {n k : ℕ} (U : Frame n k) (v : Fin n → ℝ) :
    0 ≤ gramVariance U v := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Ordinary frame contraction, with no positive-row assumption. -/
theorem gramVariance_le {n k : ℕ} (U : Frame n k) (v : Fin n → ℝ) :
    gramVariance U v ≤ ∑ i, leverage U i * v i ^ 2 := by
  rw [gramVariance_identity]
  exact sub_le_self _ (gramSchurForm_nonneg U v)

end CubeSections
