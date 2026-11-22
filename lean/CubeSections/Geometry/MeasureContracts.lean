import CubeSections.Geometry.Boundary
import CubeSections.Geometry.AffineSections

/-! Explicit mass and real-volume consequences of the boundary contracts. -/
noncomputable section
open Set MeasureTheory
namespace CubeSections

theorem frame_openSlab_mass {n k : ℕ} (U : Frame n k) :
    volume {x : E k | ∀ i, |(U x) i| < (1 : ℝ) / 2} = sectionMass U :=
  (measure_congr (frame_closed_open_slabs_ae U)).symm

theorem frame_openSlab_volume {n k : ℕ} (U : Frame n k) :
    (volume {x : E k | ∀ i, |(U x) i| < (1 : ℝ) / 2}).toReal = sectionVolume U := by
  rw [frame_openSlab_mass]
  rfl

end CubeSections
