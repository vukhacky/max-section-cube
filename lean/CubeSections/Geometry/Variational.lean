import CubeSections.Geometry.RowChanges
import CubeSections.Geometry.Continuity

/-!
# Volume comparisons from actual row modifications

Raw slab inclusion is converted to a normalized-frame comparison with the exact
Gram determinant. At a maximizing frame this yields the ordered replacement
inequalities and hence the symmetric leverage-gap inequality.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal Matrix

namespace CubeSections

theorem sectionVolume_le_rawVolume_of_subset {n m k : ℕ}
    (U : Frame n k) (R : E k →ₗ[ℝ] E m) (hR : Function.Injective R)
    (hsub : U ⁻¹' cube n ⊆ rawSlab R) : sectionVolume U ≤ rawVolume R :=
  ENNReal.toReal_mono (rawMass_ne_top R hR) (measure_mono hsub)

theorem normalizedFrame_volume_ge_of_subset {n m k : ℕ}
    (U : Frame n k) (R : E k →ₗ[ℝ] E m) (hR : Function.Injective R)
    (hsub : U ⁻¹' cube n ⊆ rawSlab R) :
    R.normDet * sectionVolume U ≤ sectionVolume (normalizedFrame R hR) := by
  rw [sectionVolume_eq_normDet_mul_rawVolume R (normalizedFrame R hR)
    (normalizedFrame_range R hR)]
  exact mul_le_mul_of_nonneg_left (sectionVolume_le_rawVolume_of_subset U R hR hsub)
    R.normDet_nonneg

theorem normDet_le_one_of_maximizing {n k : ℕ} (U : Frame n k)
    (hU : IsMaximizingFrame U) (R : E k →ₗ[ℝ] E n) (hR : Function.Injective R)
    (hsub : U ⁻¹' cube n ⊆ rawSlab R) : R.normDet ≤ 1 := by
  have h := (normalizedFrame_volume_ge_of_subset U R hR hsub).trans
    (hU (normalizedFrame R hR))
  have h' : R.normDet * sectionVolume U ≤ 1 * sectionVolume U := by simpa using h
  exact (mul_le_mul_iff_left₀ (sectionVolume_pos U)).mp (by simpa [mul_comm] using h')

theorem rawMatrix_det_le_one_of_maximizing {n k : ℕ} (U : Frame n k)
    (hU : IsMaximizingFrame U) (R : E k →ₗ[ℝ] E n) (hR : Function.Injective R)
    (hsub : U ⁻¹' cube n ⊆ rawSlab R) :
    Matrix.det ((rawMatrix R).transpose * rawMatrix R) ≤ 1 := by
  rw [← normDet_sq_eq_det_rawMatrix]
  have h := normDet_le_one_of_maximizing U hU R hR hsub
  nlinarith [R.normDet_nonneg]

theorem maximizing_replaceRow_det_le_one {n k : ℕ} (U : Frame n k)
    (hU : IsMaximizingFrame U) (i j : Fin n) (hi : leverage U i < 1) :
    Matrix.det (1 - Matrix.vecMulVec (frameMatrix U i) (frameMatrix U i) +
      Matrix.vecMulVec (frameMatrix U j) (frameMatrix U j)) ≤ 1 := by
  rw [← replaceRowMap_gram]
  exact rawMatrix_det_le_one_of_maximizing U hU (replaceRowMap U i j)
    (replaceRowMap_injective U i j hi) (section_subset_replaceRowMap_slab U i j)

theorem maximizing_leverage_gap {n k : ℕ} (U : Frame n k)
    (hU : IsMaximizingFrame U) (i j : Fin n)
    (hi : leverage U i < 1) (hj : leverage U j < 1) :
    |leverage U i - leverage U j| ≤
      leverage U i * leverage U j - (gramProjection U i j) ^ 2 :=
  leverage_gap_of_rowReplacement_det_le U i j
    (maximizing_replaceRow_det_le_one U hU i j hi)
    (maximizing_replaceRow_det_le_one U hU j i hj)

theorem duplicateRow_normalized_volume {n k : ℕ} (U : Frame n k) (i : Fin n) :
    sectionVolume (normalizedFrame (duplicateRowMap U i) (duplicateRowMap_injective U i)) =
      Real.sqrt (1 + leverage U i) * sectionVolume U := by
  rw [normalizedFrame_sectionVolume_rawMatrix, duplicateRowMap_det]
  have h : rawVolume (duplicateRowMap U i) = sectionVolume U := by
    unfold rawVolume rawMass sectionVolume sectionMass
    rw [duplicateRowMap_slab]
  rw [h]

theorem deleteRow_normalized_volume_lower {n k : ℕ} (U : Frame (n + 1) k)
    (i : Fin (n + 1)) (hi : leverage U i < 1) :
    Real.sqrt (1 - leverage U i) * sectionVolume U ≤
      sectionVolume (normalizedFrame (deleteRowMap U i) (deleteRowMap_injective U i hi)) := by
  have h := normalizedFrame_volume_ge_of_subset U (deleteRowMap U i)
    (deleteRowMap_injective U i hi) (section_subset_deleteRowMap_slab U i)
  rw [normDet_eq_sqrt_det_rawMatrix, deleteRowMap_det] at h
  exact h

end CubeSections
