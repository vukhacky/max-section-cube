import CubeSections.Geometry.RawMatrix
import CubeSections.LinearAlgebra.RankUpdate
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Actual raw row modifications and their Gram determinants. -/

noncomputable section
open Set MeasureTheory Finset
open scoped Matrix ENNReal

namespace CubeSections

def replaceRowMap {n k : ℕ} (U : Frame n k) (i j : Fin n) : E k →ₗ[ℝ] E n where
  toFun x := WithLp.toLp 2 (fun p => if p = i then (U x) j else (U x) p)
  map_add' x y := by
    ext p
    by_cases hp : p = i <;> simp [hp]
  map_smul' c x := by
    ext p
    by_cases hp : p = i <;> simp [hp]

@[simp] theorem replaceRowMap_apply {n k : ℕ} (U : Frame n k) (i j p : Fin n) (x : E k) :
    (replaceRowMap U i j x) p = if p = i then (U x) j else (U x) p := rfl

theorem rawMatrix_replaceRowMap {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    rawMatrix (replaceRowMap U i j) = (frameMatrix U).updateRow i (frameMatrix U j) := by
  ext p a
  simp [rawMatrix, Matrix.updateRow_apply, frameMatrix]

theorem transpose_mul_updateRow {n k : ℕ} (M : Matrix (Fin n) (Fin k) ℝ)
    (i : Fin n) (v : Fin k → ℝ) :
    (M.updateRow i v).transpose * M.updateRow i v =
      M.transpose * M - Matrix.vecMulVec (M i) (M i) + Matrix.vecMulVec v v := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.vecMulVec_apply]
  have hf : (fun p => (M.updateRow i v) p a * (M.updateRow i v) p b) =
      Function.update (fun p => M p a * M p b) i (v a * v b) := by
    funext p
    by_cases hp : p = i <;> simp [Matrix.updateRow_apply, hp]
  rw [hf, Finset.sum_update_of_mem (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase]
  have hs := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun p => M p a * M p b) (Finset.mem_univ i)
  linarith

theorem replaceRowMap_gram {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    (rawMatrix (replaceRowMap U i j)).transpose * rawMatrix (replaceRowMap U i j) =
      1 - Matrix.vecMulVec (frameMatrix U i) (frameMatrix U i) +
        Matrix.vecMulVec (frameMatrix U j) (frameMatrix U j) := by
  rw [rawMatrix_replaceRowMap, transpose_mul_updateRow, frameMatrix_transpose_mul]

theorem replaceRowMap_det {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    Matrix.det ((rawMatrix (replaceRowMap U i j)).transpose * rawMatrix (replaceRowMap U i j)) =
      1 - leverage U i + leverage U j - leverage U i * leverage U j +
        (gramProjection U i j) ^ 2 := by
  rw [replaceRowMap_gram, det_replace_row]

theorem replaceRowMap_det_pos {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hi : leverage U i < 1) :
    0 < Matrix.det ((rawMatrix (replaceRowMap U i j)).transpose * rawMatrix (replaceRowMap U i j)) := by
  rw [replaceRowMap_det]
  have h₁ : 0 < 1 - leverage U i := sub_pos.mpr hi
  have h₂ : 0 < 1 + leverage U j := by linarith [leverage_nonneg U j]
  nlinarith [mul_pos h₁ h₂, sq_nonneg (gramProjection U i j)]

theorem replaceRowMap_injective {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hi : leverage U i < 1) : Function.Injective (replaceRowMap U i j) :=
  injective_of_rawMatrix_det_pos _ (replaceRowMap_det_pos U i j hi)

theorem section_subset_replaceRowMap_slab {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    U ⁻¹' cube n ⊆ rawSlab (replaceRowMap U i j) := by
  intro x hx
  change ∀ p, |(replaceRowMap U i j x) p| ≤ (1 : ℝ) / 2
  intro p
  rw [replaceRowMap_apply]
  split_ifs <;> exact hx _

def duplicateRowMap {n k : ℕ} (U : Frame n k) (i : Fin n) : E k →ₗ[ℝ] E (n + 1) where
  toFun x := WithLp.toLp 2 (Fin.cons ((U x) i) (fun p => (U x) p))
  map_add' x y := by
    ext p
    refine Fin.cases ?_ (fun j => ?_) p <;> simp
  map_smul' c x := by
    ext p
    refine Fin.cases ?_ (fun j => ?_) p <;> simp

@[simp] theorem duplicateRowMap_zero {n k : ℕ} (U : Frame n k) (i : Fin n) (x : E k) :
    (duplicateRowMap U i x) 0 = (U x) i := rfl

@[simp] theorem duplicateRowMap_succ {n k : ℕ} (U : Frame n k) (i j : Fin n) (x : E k) :
    (duplicateRowMap U i x) j.succ = (U x) j := rfl

theorem duplicateRowMap_gram {n k : ℕ} (U : Frame n k) (i : Fin n) :
    (rawMatrix (duplicateRowMap U i)).transpose * rawMatrix (duplicateRowMap U i) =
      1 + Matrix.vecMulVec (frameMatrix U i) (frameMatrix U i) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, rawMatrix,
    duplicateRowMap_zero, duplicateRowMap_succ, Matrix.add_apply, Matrix.vecMulVec_apply]
  have h := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M a b)
    (frameMatrix_transpose_mul U)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, frameMatrix] at h
  rw [h]
  exact add_comm _ _

theorem duplicateRowMap_det {n k : ℕ} (U : Frame n k) (i : Fin n) :
    Matrix.det ((rawMatrix (duplicateRowMap U i)).transpose * rawMatrix (duplicateRowMap U i)) =
      1 + leverage U i := by
  rw [duplicateRowMap_gram, det_duplicate_row]

theorem duplicateRowMap_injective {n k : ℕ} (U : Frame n k) (i : Fin n) :
    Function.Injective (duplicateRowMap U i) := by
  apply injective_of_rawMatrix_det_pos
  rw [duplicateRowMap_det]
  linarith [leverage_nonneg U i]

theorem duplicateRowMap_slab {n k : ℕ} (U : Frame n k) (i : Fin n) :
    rawSlab (duplicateRowMap U i) = U ⁻¹' cube n := by
  ext x
  constructor
  · intro h j
    exact h j.succ
  · intro h j
    refine Fin.cases ?_ (fun p => ?_) j
    · exact h i
    · exact h p

def deleteRowMap {n k : ℕ} (U : Frame (n + 1) k) (i : Fin (n + 1)) : E k →ₗ[ℝ] E n where
  toFun x := WithLp.toLp 2 (fun p => (U x) (i.succAbove p))
  map_add' x y := by ext p; simp
  map_smul' c x := by ext p; simp

@[simp] theorem deleteRowMap_apply {n k : ℕ} (U : Frame (n + 1) k)
    (i : Fin (n + 1)) (p : Fin n) (x : E k) :
    (deleteRowMap U i x) p = (U x) (i.succAbove p) := rfl

theorem deleteRowMap_gram {n k : ℕ} (U : Frame (n + 1) k) (i : Fin (n + 1)) :
    (rawMatrix (deleteRowMap U i)).transpose * rawMatrix (deleteRowMap U i) =
      1 - Matrix.vecMulVec (frameMatrix U i) (frameMatrix U i) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rawMatrix, deleteRowMap_apply,
    Matrix.sub_apply, Matrix.vecMulVec_apply]
  have h := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M a b)
    (frameMatrix_transpose_mul U)
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
  rw [Fin.sum_univ_succAbove (fun p => frameMatrix U p a * frameMatrix U p b) i] at h
  simp only [frameMatrix] at h ⊢
  linarith

theorem deleteRowMap_det {n k : ℕ} (U : Frame (n + 1) k) (i : Fin (n + 1)) :
    Matrix.det ((rawMatrix (deleteRowMap U i)).transpose * rawMatrix (deleteRowMap U i)) =
      1 - leverage U i := by
  rw [deleteRowMap_gram, det_delete_row]

theorem deleteRowMap_injective {n k : ℕ} (U : Frame (n + 1) k) (i : Fin (n + 1))
    (hi : leverage U i < 1) : Function.Injective (deleteRowMap U i) := by
  apply injective_of_rawMatrix_det_pos
  rw [deleteRowMap_det]
  exact sub_pos.mpr hi

theorem section_subset_deleteRowMap_slab {n k : ℕ} (U : Frame (n + 1) k)
    (i : Fin (n + 1)) : U ⁻¹' cube (n + 1) ⊆ rawSlab (deleteRowMap U i) := by
  intro x hx j
  exact hx (i.succAbove j)

end CubeSections
