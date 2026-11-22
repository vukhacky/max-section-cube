import CubeSections.Geometry.Endpoints

/-! The internal zero-dimensional convention: a nonempty point section has mass one. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubeSections

theorem zeroDimension_preimage {n : ℕ} (U : Frame n 0) : U ⁻¹' cube n = Set.univ := by
  ext x
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  simp [cube]

theorem zeroDimension_sectionMass {n : ℕ} (U : Frame n 0) : sectionMass U = 1 := by
  calc
    sectionMass U = sectionMass (singletonData 0).frame := by
      unfold sectionMass
      rw [zeroDimension_preimage, zeroDimension_preimage]
    _ = 1 := by rw [BlockData.sectionMass_frame]; simp

theorem zeroDimension_sectionVolume {n : ℕ} (U : Frame n 0) : sectionVolume U = 1 := by
  unfold sectionVolume
  rw [zeroDimension_sectionMass]
  simp

end CubeSections
