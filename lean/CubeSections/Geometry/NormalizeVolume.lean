import CubeSections.Semantics

/-!
# A determinant change of variables for slab intersections

The raw linear map need not be an isometry.  The normalization hypothesis records
an actual invertible change of variables, so the Jacobian cannot be omitted.
No upper bound for cube sections is assumed in this file.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubeSections

def rawSlab {n k : ℕ} (R : E k →ₗ[ℝ] E n) : Set (E k) := R ⁻¹' cube n

def rawMass {n k : ℕ} (R : E k →ₗ[ℝ] E n) : ℝ≥0∞ := volume (rawSlab R)

def rawVolume {n k : ℕ} (R : E k →ₗ[ℝ] E n) : ℝ := (rawMass R).toReal

theorem rawSlab_eq_preimage_of_normalized {n k : ℕ}
    (R : E k →ₗ[ℝ] E n) (U : Frame n k) (A : E k ≃ₗ[ℝ] E k)
    (h : ∀ x, U (A x) = R x) : rawSlab R = A ⁻¹' (U ⁻¹' cube n) := by
  ext x
  change R x ∈ cube n ↔ U (A x) ∈ cube n
  rw [h]

theorem section_eq_image_rawSlab {n k : ℕ}
    (R : E k →ₗ[ℝ] E n) (U : Frame n k) (A : E k ≃ₗ[ℝ] E k)
    (h : ∀ x, U (A x) = R x) : U ⁻¹' cube n = A '' rawSlab R := by
  rw [rawSlab_eq_preimage_of_normalized R U A h]
  exact (Set.image_preimage_eq _ A.surjective).symm

theorem rawSlab_compact_of_normalized {n k : ℕ}
    (R : E k →ₗ[ℝ] E n) (U : Frame n k) (A : E k ≃ₗ[ℝ] E k)
    (h : ∀ x, U (A x) = R x) : IsCompact (rawSlab R) := by
  rw [rawSlab_eq_preimage_of_normalized R U A h]
  exact A.toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr
    (U.isometry.isClosedEmbedding.isCompact_preimage (cube_compact n))

theorem sectionMass_normalized {n k : ℕ}
    (R : E k →ₗ[ℝ] E n) (U : Frame n k) (A : E k ≃ₗ[ℝ] E k)
    (h : ∀ x, U (A x) = R x) :
    sectionMass U = ENNReal.ofReal |LinearMap.det (A : E k →ₗ[ℝ] E k)| * rawMass R := by
  unfold sectionMass rawMass
  rw [section_eq_image_rawSlab R U A h]
  exact volume.addHaar_image_linearMap (A : E k →ₗ[ℝ] E k) (rawSlab R)

theorem rawMass_ne_top_of_normalized {n k : ℕ}
    (R : E k →ₗ[ℝ] E n) (U : Frame n k) (A : E k ≃ₗ[ℝ] E k)
    (h : ∀ x, U (A x) = R x) : rawMass R ≠ ∞ :=
  (rawSlab_compact_of_normalized R U A h).measure_ne_top

theorem rawMass_pos_of_normalized {n k : ℕ}
    (R : E k →ₗ[ℝ] E n) (U : Frame n k) (A : E k ≃ₗ[ℝ] E k)
    (h : ∀ x, U (A x) = R x) : 0 < rawMass R := by
  by_contra hn
  have hz : rawMass R = 0 := le_antisymm (le_of_not_gt hn) bot_le
  have hm := sectionMass_normalized R U A h
  rw [hz, mul_zero] at hm
  exact (ne_of_gt (sectionMass_pos U)) hm

theorem rawVolume_pos_of_normalized {n k : ℕ}
    (R : E k →ₗ[ℝ] E n) (U : Frame n k) (A : E k ≃ₗ[ℝ] E k)
    (h : ∀ x, U (A x) = R x) : 0 < rawVolume R :=
  ENNReal.toReal_pos (ne_of_gt (rawMass_pos_of_normalized R U A h))
    (rawMass_ne_top_of_normalized R U A h)

theorem sectionVolume_normalized {n k : ℕ}
    (R : E k →ₗ[ℝ] E n) (U : Frame n k) (A : E k ≃ₗ[ℝ] E k)
    (h : ∀ x, U (A x) = R x) :
    sectionVolume U = |LinearMap.det (A : E k →ₗ[ℝ] E k)| * rawVolume R := by
  unfold sectionVolume rawVolume
  rw [sectionMass_normalized R U A h, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]

theorem sectionVolume_normalized_of_det_nonneg {n k : ℕ}
    (R : E k →ₗ[ℝ] E n) (U : Frame n k) (A : E k ≃ₗ[ℝ] E k)
    (h : ∀ x, U (A x) = R x) (hd : 0 ≤ LinearMap.det (A : E k →ₗ[ℝ] E k)) :
    sectionVolume U = LinearMap.det (A : E k →ₗ[ℝ] E k) * rawVolume R := by
  rw [sectionVolume_normalized R U A h, abs_of_nonneg hd]

theorem sectionVolume_normalized_of_det_sq {n k : ℕ}
    (R : E k →ₗ[ℝ] E n) (U : Frame n k) (A : E k ≃ₗ[ℝ] E k)
    (h : ∀ x, U (A x) = R x) (d : ℝ)
    (hd : LinearMap.det (A : E k →ₗ[ℝ] E k) ^ 2 = d) :
    sectionVolume U = Real.sqrt d * rawVolume R := by
  rw [sectionVolume_normalized R U A h, ← hd, Real.sqrt_sq_eq_abs]

end CubeSections
