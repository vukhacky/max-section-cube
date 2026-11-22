import CubeSections.LinearAlgebra.Gram

/-! Actual Euclidean row vectors and normalized directions on the positive support. -/

noncomputable section
open scoped Matrix

namespace CubeSections

theorem frame_coordinate_eq_dotProduct {n k : ℕ} (U : Frame n k) (i : Fin n) (x : E k) :
    (U x) i = frameMatrix U i ⬝ᵥ x.ofLp := by
  have h := congrArg (fun z : E k => (U z) i)
    ((EuclideanSpace.basisFun (Fin k) ℝ).sum_repr x)
  simpa only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, EuclideanSpace.basisFun_repr, smul_eq_mul, frameMatrix,
    dotProduct, mul_comm] using h.symm

def rowVector {n k : ℕ} (U : Frame n k) (i : Fin n) : E k :=
  WithLp.toLp 2 (frameMatrix U i)

@[simp] theorem rowVector_apply {n k : ℕ} (U : Frame n k) (i : Fin n) (j : Fin k) :
    rowVector U i j = frameMatrix U i j := rfl

theorem rowVector_norm_sq {n k : ℕ} (U : Frame n k) (i : Fin n) :
    ‖rowVector U i‖ ^ 2 = leverage U i := by
  rw [EuclideanSpace.real_norm_sq_eq, leverage_eq_sum_sq]
  rfl

theorem rowVector_norm {n k : ℕ} (U : Frame n k) (i : Fin n) :
    ‖rowVector U i‖ = Real.sqrt (leverage U i) := by
  rw [← rowVector_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem rowVector_inner {n k : ℕ} (U : Frame n k) (i : Fin n) (x : E k) :
    inner ℝ (rowVector U i) x = (U x) i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, frame_coordinate_eq_dotProduct]
  simp [rowVector, dotProduct_comm]

theorem inner_rowVector_rowVector {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    inner ℝ (rowVector U i) (rowVector U j) = gramProjection U i j := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, rowVector, gramProjection,
    Matrix.mul_apply, dotProduct, mul_comm]

theorem rowVector_quadratic_sum {n k : ℕ} (U : Frame n k) (x : E k) :
    ∑ i, (inner ℝ (rowVector U i) x) ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [rowVector_inner]
  rw [← EuclideanSpace.real_norm_sq_eq, U.norm_map]

def ActiveRow {n k : ℕ} (U : Frame n k) := {i : Fin n // 0 < leverage U i}

def unitRow {n k : ℕ} (U : Frame n k) (i : ActiveRow U) : E k :=
  (Real.sqrt (leverage U i.val))⁻¹ • rowVector U i.val

theorem unitRow_norm {n k : ℕ} (U : Frame n k) (i : ActiveRow U) : ‖unitRow U i‖ = 1 := by
  rw [unitRow, norm_smul, rowVector_norm, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr i.property))

theorem unitRow_coordinate {n k : ℕ} (U : Frame n k) (i : ActiveRow U) (x : E k) :
    (U x) i.val = Real.sqrt (leverage U i.val) * inner ℝ (unitRow U i) x := by
  rw [unitRow, real_inner_smul_left, rowVector_inner, ← mul_assoc,
    mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr i.property)), one_mul]

end CubeSections
