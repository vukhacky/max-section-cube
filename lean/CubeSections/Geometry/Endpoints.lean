import CubeSections.Geometry.BlockVolume
import CubeSections.Geometry.Invariance

/-!
# The full-dimensional endpoint and singleton blocks
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace CubeSections

def singletonData (n : ℕ) : BlockData n n where
  block := id
  onto := Function.surjective_id
  negative := fun _ => false

@[simp] theorem singletonData_blockSize {n : ℕ} (j : Fin n) :
    (singletonData n).blockSize j = 1 := by
  have h : Finset.univ.filter (fun i : Fin n => i = j) = {j} := by
    ext i
    simp
  change (Finset.univ.filter (fun i : Fin n => i = j)).card = 1
  rw [h]
  exact Finset.card_singleton j

theorem singletonData_isBalanced (n : ℕ) (hn : 0 < n) :
    (singletonData n).IsBalanced := by
  intro j
  left
  simp [Nat.div_self hn]

theorem fullDimension_surjective {n : ℕ} (U : Frame n n) : Function.Surjective U :=
  (LinearMap.injective_iff_surjective (f := U.toLinearMap)).mp U.injective

theorem fullDimension_range {n : ℕ} (U : Frame n n) : Set.range U = Set.univ :=
  Set.range_eq_univ.mpr (fullDimension_surjective U)

theorem singletonData_volume (n : ℕ) : sectionVolume (singletonData n).frame = 1 := by
  rw [BlockData.sectionVolume_frame]
  simp

theorem fullDimension_sectionVolume {n : ℕ} (U : Frame n n) : sectionVolume U = 1 := by
  calc
    sectionVolume U = sectionVolume (singletonData n).frame :=
      sectionVolume_eq_of_range_eq
        ((fullDimension_range U).trans (fullDimension_range (singletonData n).frame).symm)
    _ = 1 := singletonData_volume n

theorem fullDimension_isBalancedSection {n : ℕ} (U : Frame n n) (hn : 0 < n) :
    IsBalancedSection U := by
  apply (isBalancedSection_iff_of_range_eq
    ((fullDimension_range U).trans (fullDimension_range (singletonData n).frame).symm)).mpr
  exact (singletonData n).isBalancedSection_frame (singletonData_isBalanced n hn)

theorem fullDimension_sectionVolume_eq_sharp {n : ℕ} (U : Frame n n) (hn : 0 < n) :
    sectionVolume U = sharpValue n n := by
  rw [fullDimension_sectionVolume]
  simp only [sharpValue, Nat.div_self hn, Nat.mod_self, Nat.sub_zero,
    one_pow, pow_zero, mul_one, Nat.cast_one, Real.sqrt_one]

end CubeSections
