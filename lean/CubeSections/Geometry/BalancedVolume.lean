import CubeSections.Geometry.Attainment
import CubeSections.Geometry.Invariance

/-! Every section with a signed balanced block range has the target volume. -/

noncomputable section
namespace CubeSections

theorem sectionVolume_eq_sharp_of_isBalancedSection {n k : ℕ}
    (U : Frame n k) (hU : IsBalancedSection U) :
    sectionVolume U = sharpValue n k := by
  obtain ⟨d, hd, hrange⟩ := hU
  calc
    sectionVolume U = sectionVolume d.frame :=
      sectionVolume_eq_of_range_eq (hrange.trans d.range_frame.symm)
    _ = sharpValue n k := d.sectionVolume_frame_of_balanced hd

end CubeSections
