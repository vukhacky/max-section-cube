import CubeSections.Geometry.Variational
import CubeSections.Geometry.RowVectors
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! Zero rows and parallel rows of actual maximizing frames. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal Matrix

namespace CubeSections

theorem rawMatrix_mulVec {n k : ℕ} (R : E k →ₗ[ℝ] E n) (x : E k) :
    rawMatrix R *ᵥ x.ofLp = (R x).ofLp := by
  ext i
  have h := congrArg (fun z : E k => (R z) i)
    ((EuclideanSpace.basisFun (Fin k) ℝ).sum_repr x)
  simpa only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, EuclideanSpace.basisFun_repr, smul_eq_mul, rawMatrix,
    Matrix.mulVec, dotProduct, mul_comm] using h

theorem leverage_eq_zero_iff_frameRow_eq_zero {n k : ℕ} (U : Frame n k) (i : Fin n) :
    leverage U i = 0 ↔ frameMatrix U i = 0 := by
  rw [← frameRow_dot_self, dotProduct_self_eq_zero]

theorem leverage_eq_zero_iff_coordinate_zero {n k : ℕ} (U : Frame n k) (i : Fin n) :
    leverage U i = 0 ↔ ∀ x, (U x) i = 0 := by
  rw [leverage_eq_zero_iff_frameRow_eq_zero]
  constructor
  · intro h x
    rw [frame_coordinate_eq_dotProduct, h, zero_dotProduct]
  · intro h
    funext j
    exact h (EuclideanSpace.basisFun (Fin k) ℝ j)

theorem deleteRowMap_slab_of_leverage_zero {n k : ℕ} (U : Frame (n + 1) k)
    (i : Fin (n + 1)) (hi : leverage U i = 0) :
    rawSlab (deleteRowMap U i) = U ⁻¹' cube (n + 1) := by
  apply Set.Subset.antisymm
  · intro x hx p
    by_cases hp : p = i
    · subst p
      rw [(leverage_eq_zero_iff_coordinate_zero U i).mp hi x]
      norm_num
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hp
      exact hx j
  · exact section_subset_deleteRowMap_slab U i

theorem exists_deleted_zeroRow_frame {n k : ℕ} (U : Frame (n + 1) k)
    (i : Fin (n + 1)) (hi : leverage U i = 0) :
    ∃ V : Frame n k, sectionVolume V = sectionVolume U := by
  have hlt : leverage U i < 1 := by rw [hi]; norm_num
  refine ⟨normalizedFrame (deleteRowMap U i) (deleteRowMap_injective U i hlt), ?_⟩
  rw [normalizedFrame_sectionVolume_rawMatrix, deleteRowMap_det, hi]
  simp only [sub_zero, Real.sqrt_one, one_mul]
  unfold rawVolume rawMass sectionVolume sectionMass
  rw [deleteRowMap_slab_of_leverage_zero U i hi]

theorem maximizing_parallel_leverage_eq {n k : ℕ} (U : Frame n k)
    (hU : IsMaximizingFrame U) (i j : Fin n)
    (hi : leverage U i < 1) (hj : leverage U j < 1)
    (hpar : (gramProjection U i j) ^ 2 = leverage U i * leverage U j) :
    leverage U i = leverage U j := by
  have h := maximizing_leverage_gap U hU i j hi hj
  rw [hpar, sub_self] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

theorem frameRows_eq_or_eq_neg_of_equal_leverage {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hc : leverage U i = leverage U j)
    (hpar : (gramProjection U i j) ^ 2 = leverage U i * leverage U j) :
    frameMatrix U i = frameMatrix U j ∨ frameMatrix U i = -frameMatrix U j := by
  have hs : (gramProjection U i j) ^ 2 = (leverage U i) ^ 2 := by rw [hpar, ← hc]; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hp | hp
  · left
    apply sub_eq_zero.mp
    apply dotProduct_self_eq_zero.mp
    simp only [sub_dotProduct, dotProduct_sub, frameRow_dot_self, frameRow_dot,
      gramProjection_symm U j i, hp, ← hc]
    ring
  · right
    apply eq_neg_iff_add_eq_zero.mpr
    apply dotProduct_self_eq_zero.mp
    simp only [add_dotProduct, dotProduct_add, frameRow_dot_self, frameRow_dot,
      gramProjection_symm U j i, hp, ← hc]
    ring

theorem maximizing_parallel_rows_eq_or_eq_neg {n k : ℕ} (U : Frame n k)
    (hU : IsMaximizingFrame U) (i j : Fin n)
    (hi : leverage U i < 1) (hj : leverage U j < 1)
    (hpar : (gramProjection U i j) ^ 2 = leverage U i * leverage U j) :
    frameMatrix U i = frameMatrix U j ∨ frameMatrix U i = -frameMatrix U j :=
  frameRows_eq_or_eq_neg_of_equal_leverage U i j
    (maximizing_parallel_leverage_eq U hU i j hi hj hpar) hpar

end CubeSections
