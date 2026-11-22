import CubeSections.Geometry.NormalizeVolume
import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Normalization of every injective raw slab system

An orthonormal basis of the range produces a genuine frame. The Euclidean
Hausdorff-measure change-of-variables theorem identifies its volume factor with
the square root of the Gram determinant. A positive matrix square root is not
needed for this normalization.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubeSections

def rangeOrthonormalBasis {n k : ℕ} (R : E k →ₗ[ℝ] E n)
    (hR : Function.Injective R) : OrthonormalBasis (Fin k) ℝ R.range := by
  have h : Nonempty (OrthonormalBasis (Fin (Module.finrank ℝ (E k))) ℝ R.range) :=
    (R.normDet_ne_zero_tfae.out 5 4).mp hR
  have hdim : Module.finrank ℝ (E k) = k := finrank_euclideanSpace_fin
  rw [hdim] at h
  exact Classical.choice h

def normalizedFrame {n k : ℕ} (R : E k →ₗ[ℝ] E n)
    (hR : Function.Injective R) : Frame n k :=
  R.range.subtypeₗᵢ.comp (rangeOrthonormalBasis R hR).repr.symm.toLinearIsometry

theorem normalizedFrame_range {n k : ℕ} (R : E k →ₗ[ℝ] E n)
    (hR : Function.Injective R) : Set.range (normalizedFrame R hR) = Set.range R := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ((rangeOrthonormalBasis R hR).repr.symm x).property
  · rintro ⟨x, rfl⟩
    refine ⟨(rangeOrthonormalBasis R hR).repr ⟨R x, ⟨x, rfl⟩⟩, ?_⟩
    change ↑((rangeOrthonormalBasis R hR).repr.symm
      ((rangeOrthonormalBasis R hR).repr ⟨R x, ⟨x, rfl⟩⟩)) = R x
    simp

def normalizingEquiv {n k : ℕ} (R : E k →ₗ[ℝ] E n)
    (hR : Function.Injective R) : E k ≃ₗ[ℝ] E k :=
  (LinearEquiv.ofInjective R hR).trans (rangeOrthonormalBasis R hR).repr.toLinearEquiv

theorem normalizedFrame_normalizingEquiv {n k : ℕ} (R : E k →ₗ[ℝ] E n)
    (hR : Function.Injective R) (x : E k) :
    normalizedFrame R hR (normalizingEquiv R hR x) = R x := by
  change ↑((rangeOrthonormalBasis R hR).repr.symm
    ((rangeOrthonormalBasis R hR).repr ((LinearEquiv.ofInjective R hR) x))) = R x
  simp

theorem rawSlab_compact {n k : ℕ} (R : E k →ₗ[ℝ] E n)
    (hR : Function.Injective R) : IsCompact (rawSlab R) :=
  (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hR)).isCompact_preimage
    (cube_compact n)

theorem rawMass_ne_top {n k : ℕ} (R : E k →ₗ[ℝ] E n)
    (hR : Function.Injective R) : rawMass R ≠ ∞ := (rawSlab_compact R hR).measure_ne_top

theorem sectionMass_eq_normDet_mul_rawMass {n k : ℕ}
    (R : E k →ₗ[ℝ] E n) (U : Frame n k) (h : Set.range U = Set.range R) :
    sectionMass U = ENNReal.ofReal R.normDet * rawMass R := by
  rw [sectionMass_eq_hausdorff, h, ← Set.image_preimage_eq_inter_range]
  simpa only [finrank_euclideanSpace_fin, rawSlab, rawMass] using
    R.euclideanHausdorffMeasure_image_eq_normDet_mul_volume (rawSlab R)

theorem sectionVolume_eq_normDet_mul_rawVolume {n k : ℕ}
    (R : E k →ₗ[ℝ] E n) (U : Frame n k) (h : Set.range U = Set.range R) :
    sectionVolume U = R.normDet * rawVolume R := by
  unfold sectionVolume rawVolume
  rw [sectionMass_eq_normDet_mul_rawMass R U h, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal R.normDet_nonneg]

theorem rawMass_pos {n k : ℕ} (R : E k →ₗ[ℝ] E n)
    (hR : Function.Injective R) : 0 < rawMass R :=
  rawMass_pos_of_normalized R (normalizedFrame R hR) (normalizingEquiv R hR)
    (normalizedFrame_normalizingEquiv R hR)

theorem rawVolume_pos {n k : ℕ} (R : E k →ₗ[ℝ] E n)
    (hR : Function.Injective R) : 0 < rawVolume R :=
  ENNReal.toReal_pos (ne_of_gt (rawMass_pos R hR)) (rawMass_ne_top R hR)

theorem normDet_eq_sqrt_gramDet {n k : ℕ} (R : E k →ₗ[ℝ] E n) :
    R.normDet = Real.sqrt (LinearMap.det (R.adjoint.comp R)) := by
  have h : R.normDet ^ 2 = LinearMap.det (R.adjoint.comp R) := by
    simpa using R.normDet_sq
  rw [← h, Real.sqrt_sq R.normDet_nonneg]

theorem normalizedFrame_sectionVolume {n k : ℕ} (R : E k →ₗ[ℝ] E n)
    (hR : Function.Injective R) :
    sectionVolume (normalizedFrame R hR) =
      Real.sqrt (LinearMap.det (R.adjoint.comp R)) * rawVolume R := by
  rw [sectionVolume_eq_normDet_mul_rawVolume R (normalizedFrame R hR)
    (normalizedFrame_range R hR), normDet_eq_sqrt_gramDet]

theorem exists_normalizedFrame {n k : ℕ} (R : E k →ₗ[ℝ] E n)
    (hR : Function.Injective R) :
    ∃ U : Frame n k, Set.range U = Set.range R ∧
      sectionVolume U = Real.sqrt (LinearMap.det (R.adjoint.comp R)) * rawVolume R :=
  ⟨normalizedFrame R hR, normalizedFrame_range R hR, normalizedFrame_sectionVolume R hR⟩

end CubeSections
