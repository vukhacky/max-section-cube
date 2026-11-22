import CubeSections.Geometry.Variational

/-! Orienting actual rows by cube-preserving coordinate reflections. -/

noncomputable section
open Set
open scoped Matrix

namespace CubeSections

def coordinateReflection {n : ℕ} (i : Fin n) : E n ≃ₗᵢ[ℝ] E n :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun p : Fin n =>
    if p = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

@[simp] theorem coordinateReflection_apply {n : ℕ} (i p : Fin n) (x : E n) :
    coordinateReflection i x p = if p = i then -x p else x p := by
  by_cases hp : p = i <;> simp [coordinateReflection, hp]

theorem coordinateReflection_mem_cube_iff {n : ℕ} (i : Fin n) (x : E n) :
    coordinateReflection i x ∈ cube n ↔ x ∈ cube n := by
  change (∀ p, |coordinateReflection i x p| ≤ (1 : ℝ) / 2) ↔
    (∀ p, |x p| ≤ (1 : ℝ) / 2)
  apply forall_congr'
  intro p
  by_cases hp : p = i <;> simp [hp]

def flipRowFrame {n k : ℕ} (U : Frame n k) (i : Fin n) : Frame n k :=
  (coordinateReflection i).toLinearIsometry.comp U

@[simp] theorem flipRowFrame_apply {n k : ℕ} (U : Frame n k)
    (i p : Fin n) (x : E k) :
    flipRowFrame U i x p = if p = i then -(U x) p else (U x) p :=
  coordinateReflection_apply i p (U x)

theorem flipRowFrame_preimage_cube {n k : ℕ} (U : Frame n k) (i : Fin n) :
    flipRowFrame U i ⁻¹' cube n = U ⁻¹' cube n := by
  ext x
  exact coordinateReflection_mem_cube_iff i (U x)

theorem flipRowFrame_volume {n k : ℕ} (U : Frame n k) (i : Fin n) :
    sectionVolume (flipRowFrame U i) = sectionVolume U := by
  unfold sectionVolume sectionMass
  rw [flipRowFrame_preimage_cube]

theorem flipRowFrame_maximizing {n k : ℕ} (U : Frame n k) (i : Fin n)
    (hU : IsMaximizingFrame U) : IsMaximizingFrame (flipRowFrame U i) := by
  intro V
  rw [flipRowFrame_volume]
  exact hU V

theorem frameMatrix_flipRowFrame {n k : ℕ} (U : Frame n k) (i p : Fin n) :
    frameMatrix (flipRowFrame U i) p =
      if p = i then -frameMatrix U p else frameMatrix U p := by
  ext a
  by_cases hp : p = i <;> simp [frameMatrix, hp]

theorem leverage_flipRowFrame {n k : ℕ} (U : Frame n k) (i p : Fin n) :
    leverage (flipRowFrame U i) p = leverage U p := by
  rw [← frameRow_dot_self, frameMatrix_flipRowFrame]
  split_ifs <;> simp [neg_dotProduct, dotProduct_neg, frameRow_dot_self]

theorem gramProjection_flipRowFrame {n k : ℕ} (U : Frame n k)
    (i j : Fin n) (hij : i ≠ j) :
    gramProjection (flipRowFrame U i) i j = -gramProjection U i j := by
  rw [← frameRow_dot, frameMatrix_flipRowFrame, frameMatrix_flipRowFrame,
    if_pos rfl, if_neg (Ne.symm hij), neg_dotProduct, frameRow_dot]

theorem exists_orientedFrame {n k : ℕ} (U : Frame n k)
    (i j : Fin n) (hij : i ≠ j) :
    ∃ V : Frame n k, sectionVolume V = sectionVolume U ∧
      (∀ p, leverage V p = leverage U p) ∧
      gramProjection V i j = |gramProjection U i j| ∧
      (IsMaximizingFrame U → IsMaximizingFrame V) := by
  by_cases hP : 0 ≤ gramProjection U i j
  · exact ⟨U, rfl, fun _ => rfl, (abs_of_nonneg hP).symm, fun h => h⟩
  · refine ⟨flipRowFrame U i, flipRowFrame_volume U i,
      leverage_flipRowFrame U i, ?_, flipRowFrame_maximizing U i⟩
    rw [gramProjection_flipRowFrame U i j hij, abs_of_neg (lt_of_not_ge hP)]

end CubeSections
