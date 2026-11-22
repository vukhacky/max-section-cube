import CubeSections.Analysis.FrameTransportCompact
import CubeSections.Analysis.FrameTransportOpen
import Mathlib.Topology.Connected.Clopen

/-! Global surjectivity of the actual Gaussian frame transport. -/

noncomputable section
open Set

namespace CubeSections

/-- Every Gaussian target point has an actual preimage in the open slab body.
The proof allows zero coordinate rows and zero-dimensional internal spaces. -/
theorem frameGaussianTransport_image_eq_univ {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    frameGaussianTransport U r '' frameSlabInterior U r = univ := by
  apply IsClopen.eq_univ
    ⟨frameGaussianTransport_image_isClosed U r hr, frameGaussianTransport_image_isOpen U r hr⟩
  exact ⟨frameGaussianTransport U r 0, 0, zero_mem_frameSlabInterior U r hr, rfl⟩

theorem frameGaussianTransport_surjOn {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    SurjOn (frameGaussianTransport U r) (frameSlabInterior U r) univ := by
  intro y hy
  have : y ∈ frameGaussianTransport U r '' frameSlabInterior U r := by
    rw [frameGaussianTransport_image_eq_univ U r hr]
    exact mem_univ y
  exact this

#print axioms frameGaussianTransport_image_eq_univ
#print axioms frameGaussianTransport_surjOn

end CubeSections
