import CubeSections.Analysis.FrameQuantileRegularity
import CubeSections.Analysis.FrameChangeVariables
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! Local openness of the actual Gaussian frame transport, proved from its
continuous derivative and strictly positive Jacobian. No surjectivity is used. -/

noncomputable section
open Set Filter
open scoped Topology

namespace CubeSections

theorem frameGaussianTransport_map_nhds {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) {x : E k} (hx : x ∈ frameSlabInterior U r) :
    Filter.map (frameGaussianTransport U r) (𝓝 x) = 𝓝 (frameGaussianTransport U r x) := by
  have hdet : IsUnit (frameWeightedOperator U (frameQuantileSlope U r x)).toLinearMap.det := by
    rw [frameWeightedOperator_det]
    exact isUnit_iff_ne_zero.mpr (ne_of_gt (frameGaussianJacobian_pos U r hr x))
  let e : E k ≃L[ℝ] E k := (LinearMap.equivOfIsUnitDet hdet).toContinuousLinearEquiv
  have he : (e : E k →L[ℝ] E k) = frameWeightedOperator U (frameQuantileSlope U r x) := by
    ext z
    simp [e]
  have hstrict : HasStrictFDerivAt (frameGaussianTransport U r) (e : E k →L[ℝ] E k) x := by
    rw [he]
    exact ((contDiffOn_frameGaussianTransport U r hr).contDiffAt
      ((frameSlabInterior_isOpen U r).mem_nhds hx)).hasStrictFDerivAt
      (hasFDerivAt_frameGaussianTransport U r hr hx) one_ne_zero
  exact hstrict.map_nhds_eq_of_equiv

theorem frameGaussianTransport_isOpen_image {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) {s : Set (E k)} (hs : IsOpen s)
    (hsub : s ⊆ frameSlabInterior U r) : IsOpen (frameGaussianTransport U r '' s) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  rw [← frameGaussianTransport_map_nhds U r hr (hsub hx)]
  exact image_mem_map (hs.mem_nhds hx)

theorem frameGaussianTransport_image_isOpen {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    IsOpen (frameGaussianTransport U r '' frameSlabInterior U r) :=
  frameGaussianTransport_isOpen_image U r hr (frameSlabInterior_isOpen U r) Subset.rfl

#print axioms frameGaussianTransport_map_nhds
#print axioms frameGaussianTransport_isOpen_image
#print axioms frameGaussianTransport_image_isOpen
end CubeSections
