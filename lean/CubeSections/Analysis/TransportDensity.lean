import CubeSections.Analysis.FrameSlabMeasure
import CubeSections.Analysis.FrameChangeVariables
import CubeSections.Analysis.GaussianDensity
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! The actual transported law and its density, constructed from the proved inverse
on the image and the actual change-of-variables formula. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSections

@[fun_prop] theorem measurable_frameQuantileSlope {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (i : Fin n) : Measurable (fun x => frameQuantileSlope U r x i) := by
  unfold frameQuantileSlope
  fun_prop

@[fun_prop] theorem measurable_frameGaussianJacobian {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) :
    Measurable (frameGaussianJacobian U r) := by
  have hM : Measurable (fun x => weightedGram (frameMatrix U) (frameQuantileSlope U r x)) := by
    apply measurable_pi_lambda
    intro a
    apply measurable_pi_lambda
    intro b
    simp_rw [weightedGram_apply]
    fun_prop
  exact continuous_id.matrix_det.measurable.comp hM

theorem frameGaussianTransport_measurableEmbedding {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    MeasurableEmbedding (fun x : frameSlabInterior U r => frameGaussianTransport U r x) :=
  measurableEmbedding_of_fderivWithin (frameSlabInterior_isOpen U r).measurableSet
    (fun x hx => (hasFDerivAt_frameGaussianTransport U r hr hx).hasFDerivWithinAt)
    (frameGaussianTransport_injOn U r hr)

/-- A measurable inverse on the actual image, extended arbitrarily elsewhere. -/
def frameGaussianInverse {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) : E k → E k :=
  letI : Nonempty (frameSlabInterior U r) := ⟨⟨0, zero_mem_frameSlabInterior U r hr⟩⟩
  fun y => ((frameGaussianTransport_measurableEmbedding U r hr).invFun y).val

@[fun_prop] theorem measurable_frameGaussianInverse {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : Measurable (frameGaussianInverse U r hr) := by
  letI : Nonempty (frameSlabInterior U r) := ⟨⟨0, zero_mem_frameSlabInterior U r hr⟩⟩
  exact measurable_subtypeVal.comp (frameGaussianTransport_measurableEmbedding U r hr).measurable_invFun

theorem frameGaussianInverse_transport {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) {x : E k} (hx : x ∈ frameSlabInterior U r) :
    frameGaussianInverse U r hr (frameGaussianTransport U r x) = x := by
  letI : Nonempty (frameSlabInterior U r) := ⟨⟨0, zero_mem_frameSlabInterior U r hr⟩⟩
  exact congrArg Subtype.val ((frameGaussianTransport_measurableEmbedding U r hr).leftInverse_invFun ⟨x, hx⟩)

def frameTransportedLaw {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) : Measure (E k) :=
  (frameSlabUniform U r).map (frameGaussianTransport U r)

theorem frameTransportedLaw_isProbabilityMeasure {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : IsProbabilityMeasure (frameTransportedLaw U r) := by
  letI := frameSlabUniform_isProbabilityMeasure U r hr
  unfold frameTransportedLaw
  infer_instance

theorem map_withDensity_comp_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (hf : Measurable f) (g : β → ℝ≥0∞) (hg : Measurable g) :
    (μ.withDensity (fun x => g (f x))).map f = (μ.map f).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    setLIntegral_map hs hg hf]

theorem frameSlabUniform_eq_invVolume {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    frameSlabUniform U r = ENNReal.ofReal (frameSlabVolume U r)⁻¹ • volume.restrict (frameSlabInterior U r) := by
  rw [ENNReal.ofReal_inv_of_pos (frameSlabVolume_pos U r hr)]
  simp only [frameSlabUniform, ProbabilityTheory.cond, frameSlabVolume,
    ENNReal.ofReal_toReal (frameSlabInterior_mass_ne_top U r)]

/-- Inverse Jacobian divided by the actual slab volume. -/
def frameInverseJacobianDensity {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (y : E k) : ℝ≥0∞ :=
  ENNReal.ofReal (frameSlabVolume U r * frameGaussianJacobian U r (frameGaussianInverse U r hr y))⁻¹

@[fun_prop] theorem measurable_frameInverseJacobianDensity {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : Measurable (frameInverseJacobianDensity U r hr) := by
  unfold frameInverseJacobianDensity
  fun_prop

theorem frameJacobian_inverse_density {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) {x : E k} (hx : x ∈ frameSlabInterior U r) :
    ENNReal.ofReal (frameGaussianJacobian U r x) *
        frameInverseJacobianDensity U r hr (frameGaussianTransport U r x) =
      ENNReal.ofReal (frameSlabVolume U r)⁻¹ := by
  rw [frameInverseJacobianDensity, frameGaussianInverse_transport U r hr hx,
    ← ENNReal.ofReal_mul (frameGaussianJacobian_pos U r hr x).le]
  congr 1
  field_simp [ne_of_gt (frameGaussianJacobian_pos U r hr x), ne_of_gt (frameSlabVolume_pos U r hr)]

theorem frameTransportedLaw_eq_image_density {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    frameTransportedLaw U r =
      (volume.restrict (frameGaussianTransport U r '' frameSlabInterior U r)).withDensity
        (frameInverseJacobianDensity U r hr) := by
  rw [← frameGaussianTransport_map_jacobian U r hr,
    ← map_withDensity_comp_eq _ _ (measurable_frameGaussianTransport U r) _
      (measurable_frameInverseJacobianDensity U r hr)]
  unfold frameTransportedLaw
  congr 1
  have hm := withDensity_mul (volume.restrict (frameSlabInterior U r))
    (measurable_frameGaussianJacobian U r).ennreal_ofReal
    ((measurable_frameInverseJacobianDensity U r hr).comp (measurable_frameGaussianTransport U r))
  simp only [Function.comp_def] at hm
  rw [← hm]
  rw [frameSlabUniform_eq_invVolume U r hr, ← withDensity_const]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (frameSlabInterior_isOpen U r).measurableSet] with x hx
  exact (frameJacobian_inverse_density U r hr hx).symm

/-- The transported probability density with respect to full Euclidean volume. -/
def frameTransportLebesgueDensity {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : E k → ℝ≥0∞ :=
  (frameGaussianTransport U r '' frameSlabInterior U r).indicator (frameInverseJacobianDensity U r hr)

@[fun_prop] theorem measurable_frameTransportLebesgueDensity {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : Measurable (frameTransportLebesgueDensity U r hr) :=
  (measurable_frameInverseJacobianDensity U r hr).indicator (frameGaussianTransport_image_measurable U r hr)

theorem frameTransportedLaw_eq_withDensity {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    frameTransportedLaw U r = volume.withDensity (frameTransportLebesgueDensity U r hr) := by
  rw [frameTransportedLaw_eq_image_density U r hr, frameTransportLebesgueDensity,
    withDensity_indicator (frameGaussianTransport_image_measurable U r hr)]

end CubeSections
