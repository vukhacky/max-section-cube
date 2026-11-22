import CubeSections.Geometry.GroupedFrame
import CubeSections.Geometry.StripDensity
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Rank two, an explicit right inverse, and an orthonormal parametrization of
an actual pair-coordinate kernel. No formal dimension is substituted for the
kernel until surjectivity has been proved. -/
noncomputable section
open Set Classical Module
open scoped BigOperators InnerProductSpace
namespace CubeSections

def pairCoordinateMap {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    E k →ₗ[ℝ] ℝ × ℝ where
  toFun := normalizedPairCoordinates U i j
  map_add' x y := by ext <;> simp [normalizedPairCoordinates, mul_add]
  map_smul' a x := by ext <;> simp [normalizedPairCoordinates, mul_assoc, mul_left_comm]

@[simp] theorem pairCoordinateMap_apply {n k : ℕ} (U : Frame n k)
    (i j : Fin n) (x : E k) :
    pairCoordinateMap U i j x = (2 * (U x) i, 2 * (U x) j) := rfl

def pairGramDet {n k : ℕ} (U : Frame n k) (i j : Fin n) : ℝ :=
  leverage U i * leverage U j - gramProjection U i j ^ 2

def pairRightInverse {n k : ℕ} (U : Frame n k) (i j : Fin n) (p : ℝ × ℝ) : E k :=
  ((leverage U j * p.1 - gramProjection U i j * p.2) / (2 * pairGramDet U i j)) •
      rowVector U i +
    ((leverage U i * p.2 - gramProjection U i j * p.1) / (2 * pairGramDet U i j)) •
      rowVector U j

theorem frame_rowVector_coordinate {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    (U (rowVector U j)) i = gramProjection U i j := by
  rw [← rowVector_inner, inner_rowVector_rowVector]

theorem pairCoordinateMap_rightInverse {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : pairGramDet U i j ≠ 0) :
    Function.RightInverse (pairRightInverse U i j) (pairCoordinateMap U i j) := by
  intro p
  ext <;> simp only [pairCoordinateMap_apply, pairRightInverse, map_add, map_smul,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, frame_rowVector_coordinate,
    ← gramProjection_symm U i j]
  all_goals
    dsimp
    field_simp [hdet]
    unfold pairGramDet leverage
    ring

theorem pairCoordinateMap_surjective {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : pairGramDet U i j ≠ 0) : Function.Surjective (pairCoordinateMap U i j) :=
  (pairCoordinateMap_rightInverse U i j hdet).surjective

def pairKernel {n k : ℕ} (U : Frame n k) (i j : Fin n) : Submodule ℝ (E k) :=
  (pairCoordinateMap U i j).ker

theorem mem_pairKernel {n k : ℕ} (U : Frame n k) (i j : Fin n) (x : E k) :
    x ∈ pairKernel U i j ↔ (U x) i = 0 ∧ (U x) j = 0 := by
  simp [pairKernel, LinearMap.mem_ker, Prod.ext_iff]

theorem pairKernel_finrank {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : pairGramDet U i j ≠ 0) : Module.finrank ℝ (pairKernel U i j) = k - 2 := by
  have h := (pairCoordinateMap U i j).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (pairCoordinateMap_surjective U i j hdet),
    finrank_top, Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin] at h
  change 1 + 1 + Module.finrank ℝ (pairKernel U i j) = k at h
  omega

theorem two_le_dimension_of_pairGramDet_ne_zero {n k : ℕ} (U : Frame n k)
    (i j : Fin n) (hdet : pairGramDet U i j ≠ 0) : 2 ≤ k := by
  have h := LinearMap.finrank_le_finrank_of_surjective
    (pairCoordinateMap_surjective U i j hdet)
  simpa [Module.finrank_prod, finrank_euclideanSpace_fin] using h

def pairKernelBasis {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : pairGramDet U i j ≠ 0) : OrthonormalBasis (Fin (k - 2)) ℝ (pairKernel U i j) :=
  (stdOrthonormalBasis ℝ (pairKernel U i j)).reindex
    (finCongr (pairKernel_finrank U i j hdet))

def pairKernelFrame {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : pairGramDet U i j ≠ 0) : Frame k (k - 2) :=
  (pairKernel U i j).subtypeₗᵢ.comp (pairKernelBasis U i j hdet).repr.symm.toLinearIsometry

theorem pairKernelFrame_mem {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : pairGramDet U i j ≠ 0) (x : E (k - 2)) :
    pairKernelFrame U i j hdet x ∈ pairKernel U i j :=
  ((pairKernelBasis U i j hdet).repr.symm x).property

theorem pairKernelFrame_range {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : pairGramDet U i j ≠ 0) :
    Set.range (pairKernelFrame U i j hdet) = (pairKernel U i j : Set (E k)) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact pairKernelFrame_mem U i j hdet z
  · intro hx
    refine ⟨(pairKernelBasis U i j hdet).repr ⟨x, hx⟩, ?_⟩
    change ↑((pairKernelBasis U i j hdet).repr.symm
      ((pairKernelBasis U i j hdet).repr ⟨x, hx⟩)) = x
    simp

theorem pairGramDet_classRep_pos {n k : ℕ} (U : Frame n k) (c d : RowClass U)
    (hcd : c ≠ d) :
    0 < pairGramDet U (rowClassRep U c).val (rowClassRep U d).val := by
  unfold pairGramDet
  rw [rowClassRep_gram_sq]
  change 0 < rowClassLeverage U c * rowClassLeverage U d -
    rowClassLeverage U c * rowClassLeverage U d * rowClassAngle U c d
  have hm := mul_pos (rowClassLeverage_pos U c) (rowClassLeverage_pos U d)
  nlinarith [rowClassAngle_lt_one U c d hcd]

end CubeSections
