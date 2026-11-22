import CubeSections.Geometry.Blocks

/-!
# The section depends only on the represented plane
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubeSections

theorem sectionMass_eq_of_range_eq {n k : ℕ} {U V : Frame n k}
    (h : Set.range U = Set.range V) : sectionMass U = sectionMass V := by
  rw [sectionMass_eq_hausdorff, sectionMass_eq_hausdorff, h]

theorem sectionVolume_eq_of_range_eq {n k : ℕ} {U V : Frame n k}
    (h : Set.range U = Set.range V) : sectionVolume U = sectionVolume V := by
  unfold sectionVolume
  rw [sectionMass_eq_of_range_eq h]

theorem isBalancedSection_iff_of_range_eq {n k : ℕ} {U V : Frame n k}
    (h : Set.range U = Set.range V) : IsBalancedSection U ↔ IsBalancedSection V := by
  simp only [IsBalancedSection, h]

theorem range_comp_domain_isometry {n k : ℕ} (U : Frame n k)
    (O : E k ≃ₗᵢ[ℝ] E k) :
    Set.range (U.comp O.toLinearIsometry) = Set.range U := by
  exact O.surjective.range_comp U

theorem sectionVolume_comp_domain_isometry {n k : ℕ} (U : Frame n k)
    (O : E k ≃ₗᵢ[ℝ] E k) :
    sectionVolume (U.comp O.toLinearIsometry) = sectionVolume U :=
  sectionVolume_eq_of_range_eq (range_comp_domain_isometry U O)

theorem isBalancedSection_comp_domain_isometry {n k : ℕ} (U : Frame n k)
    (O : E k ≃ₗᵢ[ℝ] E k) :
    IsBalancedSection (U.comp O.toLinearIsometry) ↔ IsBalancedSection U :=
  isBalancedSection_iff_of_range_eq (range_comp_domain_isometry U O)

end CubeSections
