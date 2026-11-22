import CubeSections.Semantics
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith

/-! Gram projection identities for the actual isometric section parametrization. -/

noncomputable section
open scoped Matrix
open Finset

namespace CubeSections

/-- Coordinate matrix of an isometry in the canonical orthonormal bases. -/
def frameMatrix {n k : ℕ} (U : Frame n k) : Matrix (Fin n) (Fin k) ℝ :=
  fun i j => (U (EuclideanSpace.basisFun (Fin k) ℝ j)) i

/-- The ambient Gram projection. -/
def gramProjection {n k : ℕ} (U : Frame n k) : Matrix (Fin n) (Fin n) ℝ :=
  frameMatrix U * (frameMatrix U).transpose

/-- Squared length of an ambient coordinate projected onto the section. -/
def leverage {n k : ℕ} (U : Frame n k) (i : Fin n) : ℝ :=
  gramProjection U i i

theorem frameMatrix_transpose_mul {n k : ℕ} (U : Frame n k) :
    (frameMatrix U).transpose * frameMatrix U = 1 := by
  ext i j
  have h := U.inner_map_map (EuclideanSpace.basisFun (Fin k) ℝ j)
    (EuclideanSpace.basisFun (Fin k) ℝ i)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [frameMatrix, Matrix.mul_apply, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, EuclideanSpace.basisFun_apply, PiLp.single_apply, Pi.single_apply,
    Matrix.one_apply, eq_comm] using h

theorem gramProjection_transpose {n k : ℕ} (U : Frame n k) :
    (gramProjection U).transpose = gramProjection U := by
  simp [gramProjection, Matrix.transpose_mul]

theorem gramProjection_mul_self {n k : ℕ} (U : Frame n k) :
    gramProjection U * gramProjection U = gramProjection U := by
  simp only [gramProjection, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (frameMatrix U).transpose,
    frameMatrix_transpose_mul, Matrix.one_mul]

theorem gramProjection_symm {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    gramProjection U i j = gramProjection U j i := by
  exact (congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j i)
    (gramProjection_transpose U))

theorem leverage_eq_sum_sq {n k : ℕ} (U : Frame n k) (i : Fin n) :
    leverage U i = ∑ j, (frameMatrix U i j) ^ 2 := by
  simp [leverage, gramProjection, Matrix.mul_apply, pow_two]

theorem leverage_nonneg {n k : ℕ} (U : Frame n k) (i : Fin n) :
    0 ≤ leverage U i := by
  rw [leverage_eq_sum_sq]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem gramProjection_row_sq_sum {n k : ℕ} (U : Frame n k) (i : Fin n) :
    ∑ j, (gramProjection U i j) ^ 2 = leverage U i := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i)
    (gramProjection_mul_self U)
  simpa [Matrix.mul_apply, ← gramProjection_symm U i, pow_two, leverage] using h

theorem leverage_le_one {n k : ℕ} (U : Frame n k) (i : Fin n) :
    leverage U i ≤ 1 := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
    sq_nonneg (gramProjection U i j)) (Finset.mem_univ i)
  rw [gramProjection_row_sq_sum U i] at h
  change leverage U i ^ 2 ≤ leverage U i at h
  nlinarith [leverage_nonneg U i]

theorem sum_leverage {n k : ℕ} (U : Frame n k) :
    ∑ i, leverage U i = (k : ℝ) := by
  change Matrix.trace (gramProjection U) = (k : ℝ)
  rw [gramProjection, Matrix.trace_mul_comm, frameMatrix_transpose_mul]
  simp

theorem gramProjection_offdiag_sq_sum {n k : ℕ} (U : Frame n k) (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i, (gramProjection U i j) ^ 2 =
      leverage U i * (1 - leverage U i) := by
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun j => (gramProjection U i j) ^ 2) (Finset.mem_univ i)
  rw [gramProjection_row_sq_sum U i] at h
  change (∑ j ∈ Finset.univ.erase i, (gramProjection U i j) ^ 2) +
    leverage U i ^ 2 = leverage U i at h
  nlinarith

end CubeSections
