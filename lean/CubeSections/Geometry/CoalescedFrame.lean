import CubeSections.Geometry.RowClasses
import CubeSections.Geometry.RowSupport
import CubeSections.LinearAlgebra.Projection

/-!
# The actual frame obtained by coalescing unoriented row classes

Each class is weighted by the sum of its row leverages. The construction therefore
works for arbitrary frames, including zero rows and unequal lengths within a class.
-/

noncomputable section
open Set Classical
open scoped BigOperators InnerProductSpace
namespace CubeSections

theorem unitRow_inner_sq_eq_classUnit {n k : ℕ} (U : Frame n k) (i : ActiveRow U) (x : E k) :
    (inner ℝ (unitRow U i) x) ^ 2 =
      (inner ℝ (rowClassUnit U (rowClass U i)) x) ^ 2 := by
  rcases unitRow_eq_signed_classUnit U i with h | h
  · rw [h]
  · rw [h, inner_neg_left, neg_sq]

theorem rowClass_quadratic_sum {n k : ℕ} (U : Frame n k) (x : E k) :
    ∑ c : RowClass U, rowClassMass U c * (inner ℝ (rowClassUnit U c) x) ^ 2 = ‖x‖ ^ 2 := by
  calc
    _ = ∑ c : RowClass U, ∑ i : ActiveRow U with rowClass U i = c,
        leverage U i.val * (inner ℝ (unitRow U i) x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro c hc
      unfold rowClassMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [unitRow_inner_sq_eq_classUnit, (Finset.mem_filter.mp hi).2]
    _ = ∑ i : ActiveRow U, leverage U i.val * (inner ℝ (unitRow U i) x) ^ 2 :=
      Finset.sum_fiberwise _ _ _
    _ = ∑ i : ActiveRow U, ((U x) i.val) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [unitRow_coordinate U i x, mul_pow, Real.sq_sqrt i.property.le]
    _ = ∑ i : Fin n, ((U x) i) ^ 2 := by
      apply sum_activeRows U (fun i => ((U x) i) ^ 2)
      intro i hi
      rw [(leverage_eq_zero_iff_coordinate_zero U i).mp hi x]
      norm_num
    _ = ‖x‖ ^ 2 := by rw [← EuclideanSpace.real_norm_sq_eq, U.norm_map]

abbrev rowClassCount {n k : ℕ} (U : Frame n k) := Fintype.card (RowClass U)

def rowClassEquiv {n k : ℕ} (U : Frame n k) : RowClass U ≃ Fin (rowClassCount U) :=
  Fintype.equivFin _

def coalescedMap {n k : ℕ} (U : Frame n k) : E k →ₗ[ℝ] E (rowClassCount U) where
  toFun x := WithLp.toLp 2 (fun j =>
    Real.sqrt (rowClassMass U ((rowClassEquiv U).symm j)) *
      inner ℝ (rowClassUnit U ((rowClassEquiv U).symm j)) x)
  map_add' x y := by
    ext j
    simp only [inner_add_right, PiLp.add_apply]
    ring
  map_smul' a x := by
    ext j
    simp only [inner_smul_right, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem coalescedMap_apply {n k : ℕ} (U : Frame n k)
    (x : E k) (j : Fin (rowClassCount U)) :
    coalescedMap U x j = Real.sqrt (rowClassMass U ((rowClassEquiv U).symm j)) *
      inner ℝ (rowClassUnit U ((rowClassEquiv U).symm j)) x := rfl

theorem coalescedMap_norm {n k : ℕ} (U : Frame n k) (x : E k) :
    ‖coalescedMap U x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [coalescedMap_apply, mul_pow, Real.sq_sqrt (rowClassMass_pos U _).le]
  calc
    _ = ∑ c : RowClass U, rowClassMass U c * (inner ℝ (rowClassUnit U c) x) ^ 2 :=
      (rowClassEquiv U).symm.sum_comp
        (fun c => rowClassMass U c * (inner ℝ (rowClassUnit U c) x) ^ 2)
    _ = ‖x‖ ^ 2 := rowClass_quadratic_sum U x

def coalescedFrame {n k : ℕ} (U : Frame n k) : Frame (rowClassCount U) k where
  toLinearMap := coalescedMap U
  norm_map' := coalescedMap_norm U

@[simp] theorem coalescedFrame_apply {n k : ℕ} (U : Frame n k)
    (x : E k) (j : Fin (rowClassCount U)) :
    coalescedFrame U x j = Real.sqrt (rowClassMass U ((rowClassEquiv U).symm j)) *
      inner ℝ (rowClassUnit U ((rowClassEquiv U).symm j)) x := rfl

theorem rowVector_coalescedFrame {n k : ℕ} (U : Frame n k) (j : Fin (rowClassCount U)) :
    rowVector (coalescedFrame U) j =
      Real.sqrt (rowClassMass U ((rowClassEquiv U).symm j)) •
        rowClassUnit U ((rowClassEquiv U).symm j) := by
  ext a
  simp only [rowVector_apply, frameMatrix, coalescedFrame_apply,
    EuclideanSpace.inner_basisFun_real, PiLp.smul_apply, smul_eq_mul]

theorem leverage_coalescedFrame {n k : ℕ} (U : Frame n k) (j : Fin (rowClassCount U)) :
    leverage (coalescedFrame U) j = rowClassMass U ((rowClassEquiv U).symm j) := by
  rw [← rowVector_norm_sq, rowVector_coalescedFrame, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), rowClassUnit_norm, mul_one,
    Real.sq_sqrt (rowClassMass_pos U _).le]

theorem rowClassMass_le_one {n k : ℕ} (U : Frame n k) (c : RowClass U) :
    rowClassMass U c ≤ 1 := by
  have h := leverage_le_one (coalescedFrame U) (rowClassEquiv U c)
  simpa only [leverage_coalescedFrame, Equiv.symm_apply_apply] using h

def classGram {n k : ℕ} (U : Frame n k) (c d : RowClass U) : ℝ :=
  gramProjection (coalescedFrame U) (rowClassEquiv U c) (rowClassEquiv U d)

theorem classGram_symm {n k : ℕ} (U : Frame n k) (c d : RowClass U) :
    classGram U c d = classGram U d c := gramProjection_symm _ _ _

theorem classGram_diag {n k : ℕ} (U : Frame n k) (c : RowClass U) :
    classGram U c c = rowClassMass U c := by
  change leverage (coalescedFrame U) (rowClassEquiv U c) = _
  rw [leverage_coalescedFrame, Equiv.symm_apply_apply]

theorem classGram_formula {n k : ℕ} (U : Frame n k) (c d : RowClass U) :
    classGram U c d = Real.sqrt (rowClassMass U c) * Real.sqrt (rowClassMass U d) *
      inner ℝ (rowClassUnit U c) (rowClassUnit U d) := by
  unfold classGram
  rw [← inner_rowVector_rowVector, rowVector_coalescedFrame, rowVector_coalescedFrame]
  simp only [Equiv.symm_apply_apply, real_inner_smul_left, inner_smul_right]
  ring

theorem classGram_sq {n k : ℕ} (U : Frame n k) (c d : RowClass U) :
    classGram U c d ^ 2 = rowClassMass U c * rowClassMass U d *
      (inner ℝ (rowClassUnit U c) (rowClassUnit U d)) ^ 2 := by
  rw [classGram_formula, mul_pow, mul_pow, Real.sq_sqrt (rowClassMass_pos U c).le,
    Real.sq_sqrt (rowClassMass_pos U d).le]

theorem classGram_row_sq_sum {n k : ℕ} (U : Frame n k) (c : RowClass U) :
    ∑ d : RowClass U, classGram U c d ^ 2 = rowClassMass U c := by
  unfold classGram
  calc
    _ = ∑ j : Fin (rowClassCount U),
        gramProjection (coalescedFrame U) (rowClassEquiv U c) j ^ 2 :=
      (rowClassEquiv U).sum_comp
        (fun j => gramProjection (coalescedFrame U) (rowClassEquiv U c) j ^ 2)
    _ = rowClassMass U c := by
      rw [gramProjection_row_sq_sum, leverage_coalescedFrame, Equiv.symm_apply_apply]

theorem classGram_complement_bound {n k : ℕ} (U : Frame n k) (c d : RowClass U)
    (hcd : c ≠ d) :
    classGram U c d ^ 2 ≤ (1 - rowClassMass U c) * (1 - rowClassMass U d) := by
  unfold classGram
  have h := gramProjection_complement_entry_sq_le (coalescedFrame U)
    (rowClassEquiv U c) (rowClassEquiv U d)
    (fun h => hcd ((rowClassEquiv U).injective h))
  simpa only [leverage_coalescedFrame, Equiv.symm_apply_apply] using h

theorem rowClass_angle_complement_bound {n k : ℕ} (U : Frame n k)
    (c d : RowClass U) (hcd : c ≠ d) :
    (inner ℝ (rowClassUnit U c) (rowClassUnit U d)) ^ 2 ≤
      ((1 - rowClassMass U c) * (1 - rowClassMass U d)) /
        (rowClassMass U c * rowClassMass U d) := by
  apply (le_div_iff₀ (mul_pos (rowClassMass_pos U c) (rowClassMass_pos U d))).mpr
  have h := classGram_complement_bound U c d hcd
  rw [classGram_sq] at h
  simpa only [mul_comm] using h

def classWeight {n k : ℕ} (U : Frame n k) (c d : RowClass U) : ℝ :=
  if c = d then 0 else classGram U c d ^ 2

theorem classWeight_nonneg {n k : ℕ} (U : Frame n k) (c d : RowClass U) :
    0 ≤ classWeight U c d := by unfold classWeight; split_ifs <;> positivity

theorem classWeight_symm {n k : ℕ} (U : Frame n k) (c d : RowClass U) :
    classWeight U c d = classWeight U d c := by
  simp only [classWeight, eq_comm, classGram_symm U c d]

theorem classWeight_degree {n k : ℕ} (U : Frame n k) (c : RowClass U) :
    ∑ d : RowClass U, classWeight U c d = rowClassMass U c * (1 - rowClassMass U c) := by
  have hp : ∀ d : RowClass U, classGram U c d ^ 2 = classWeight U c d +
      if d = c then rowClassMass U c ^ 2 else 0 := by
    intro d
    by_cases h : d = c
    · subst d
      simp [classWeight, classGram_diag]
    · simp [classWeight, h, Ne.symm h]
  have hs := classGram_row_sq_sum U c
  simp_rw [hp, Finset.sum_add_distrib] at hs
  have hd : (∑ d : RowClass U, if d = c then rowClassMass U c ^ 2 else 0) =
      rowClassMass U c ^ 2 := by simp
  rw [hd] at hs
  nlinarith

theorem classWeight_degree_multiplicity {n k : ℕ} (U : Frame n k)
    (hrep : RowReplacement U) (c : RowClass U) :
    ∑ d : RowClass U, classWeight U c d =
      ((rowClassMultiplicity U c : ℝ) * rowClassLeverage U c) *
        (1 - (rowClassMultiplicity U c : ℝ) * rowClassLeverage U c) := by
  rw [classWeight_degree, rowClassMass_eq_multiplicity_mul_leverage U hrep]

end CubeSections
