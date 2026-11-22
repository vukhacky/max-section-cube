import CubeSections.Analysis.TransportDensity
import CubeSections.Analysis.TransportIntegrand
import CubeSections.Analysis.FrameQuantileRegularity
import CubeSections.Analysis.GaussianDominated
import CubeSections.Analysis.PositiveGaussianLaw

/-! The actual real inverse-Jacobian density of the frame transport.  The
intermediate statements isolate only global coverage and local openness;
neither is silently postulated as a mathematical axiom. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace CubeSections

def frameTransportRealDensity {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (y : E k) : ℝ :=
  (frameSlabVolume U r * frameGaussianJacobian U r (frameGaussianInverse U r hr y))⁻¹

theorem frameTransportRealDensity_pos {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (y : E k) : 0 < frameTransportRealDensity U r hr y := by
  exact inv_pos.mpr (mul_pos (frameSlabVolume_pos U r hr)
    (frameGaussianJacobian_pos U r hr _))

theorem frameGaussianInverse_mem_of_image_eq_univ {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i)
    (himage : frameGaussianTransport U r '' frameSlabInterior U r = univ) (y : E k) :
    frameGaussianInverse U r hr y ∈ frameSlabInterior U r := by
  have hy : y ∈ frameGaussianTransport U r '' frameSlabInterior U r := by rw [himage]; trivial
  obtain ⟨x, hx, rfl⟩ := hy
  rw [frameGaussianInverse_transport U r hr hx]
  exact hx

theorem frameGaussianTransport_inverse_of_image_eq_univ {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i)
    (himage : frameGaussianTransport U r '' frameSlabInterior U r = univ) (y : E k) :
    frameGaussianTransport U r (frameGaussianInverse U r hr y) = y := by
  have hy : y ∈ frameGaussianTransport U r '' frameSlabInterior U r := by rw [himage]; trivial
  obtain ⟨x, hx, rfl⟩ := hy
  rw [frameGaussianInverse_transport U r hr hx]

theorem frameGaussianInverse_continuous_of_image_open {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i)
    (himage : frameGaussianTransport U r '' frameSlabInterior U r = univ)
    (hopen : ∀ s : Set (E k), IsOpen s → s ⊆ frameSlabInterior U r →
      IsOpen (frameGaussianTransport U r '' s)) : Continuous (frameGaussianInverse U r hr) := by
  rw [continuous_def]
  intro s hs
  have heq : frameGaussianInverse U r hr ⁻¹' s =
      frameGaussianTransport U r '' (s ∩ frameSlabInterior U r) := by
    ext y
    constructor
    · intro hy
      exact ⟨frameGaussianInverse U r hr y,
        ⟨hy, frameGaussianInverse_mem_of_image_eq_univ U r hr himage y⟩,
        frameGaussianTransport_inverse_of_image_eq_univ U r hr himage y⟩
    · rintro ⟨x, ⟨hxs,hxK⟩, rfl⟩
      change frameGaussianInverse U r hr (frameGaussianTransport U r x) ∈ s
      rwa [frameGaussianInverse_transport U r hr hxK]
  rw [heq]
  exact hopen _ (hs.inter (frameSlabInterior_isOpen U r)) inter_subset_right

theorem continuousOn_frameGaussianJacobian {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    ContinuousOn (frameGaussianJacobian U r) (frameSlabInterior U r) := by
  have hM : ContinuousOn (fun x => weightedGram (frameMatrix U) (frameQuantileSlope U r x))
      (frameSlabInterior U r) := by
    apply continuousOn_pi.mpr
    intro a
    apply continuousOn_pi.mpr
    intro b
    simp_rw [weightedGram_apply]
    exact continuousOn_finsetSum _ (fun i _ =>
      (continuousOn_const.mul (continuousOn_frameQuantileSlope U r hr i)).mul continuousOn_const)
  exact continuous_id.matrix_det.comp_continuousOn hM

theorem frameTransportRealDensity_continuous_of_inverse {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i)
    (himage : frameGaussianTransport U r '' frameSlabInterior U r = univ)
    (hinv : Continuous (frameGaussianInverse U r hr)) :
    Continuous (frameTransportRealDensity U r hr) := by
  have hJ : Continuous (fun y => frameGaussianJacobian U r (frameGaussianInverse U r hr y)) :=
    (continuousOn_frameGaussianJacobian U r hr).comp_continuous hinv
      (frameGaussianInverse_mem_of_image_eq_univ U r hr himage)
  exact (continuous_const.mul hJ).inv₀ (fun y => ne_of_gt
    (mul_pos (frameSlabVolume_pos U r hr) (frameGaussianJacobian_pos U r hr _)))

theorem frameTransportRealDensity_le_gaussian_of_image_eq_univ {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (himage : frameGaussianTransport U r '' frameSlabInterior U r = univ) (y : E k) :
    frameTransportRealDensity U r hr y ≤
      (Real.exp (frameSlabLogFactor U r) / frameSlabVolume U r) * euclideanGaussianDensity k y := by
  let x := frameGaussianInverse U r hr y
  have hJ := frameGaussianJacobian_pos U r hr x
  have hV := frameSlabVolume_pos U r hr
  have hlower := frameTransport_density_jacobian_lower U r hr x
  rw [frameGaussianTransport_inverse_of_image_eq_univ U r hr himage y] at hlower
  have hjinv : (frameGaussianJacobian U r x)⁻¹ ≤
      Real.exp (frameSlabLogFactor U r) * euclideanGaussianDensity k y := by
    apply (inv_le_iff_one_le_mul₀ hJ).mpr
    calc
      1 = Real.exp (frameSlabLogFactor U r) * Real.exp (-frameSlabLogFactor U r) := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      _ ≤ Real.exp (frameSlabLogFactor U r) *
          (frameGaussianJacobian U r x * euclideanGaussianDensity k y) :=
        mul_le_mul_of_nonneg_left hlower (Real.exp_pos _).le
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_left hjinv (inv_pos.mpr hV).le
  simpa only [frameTransportRealDensity, x, mul_inv_rev, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using hh

theorem frameTransportRealDensity_gaussianDominated_of_image_eq_univ {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (himage : frameGaussianTransport U r '' frameSlabInterior U r = univ) :
    GaussianDominated (frameTransportRealDensity U r hr) := by
  refine ⟨(Real.exp (frameSlabLogFactor U r) / frameSlabVolume U r) *
      Real.exp (-(k : ℝ) * Real.log (Real.sqrt (2 * Real.pi))), (1/2 : ℝ),
      mul_pos (div_pos (Real.exp_pos _) (frameSlabVolume_pos U r hr)) (Real.exp_pos _), by norm_num, ?_⟩
  intro y
  rw [abs_of_pos (frameTransportRealDensity_pos U r hr y)]
  convert frameTransportRealDensity_le_gaussian_of_image_eq_univ U r hr himage y using 1
  rw [← Real.exp_log (euclideanGaussianDensity_pos k y), log_euclideanGaussianDensity,
    sub_eq_add_neg, Real.exp_add]
  rw [show -(1/2 : ℝ) * ‖y‖^2 = -(‖y‖^2/2) by ring]
  ring

theorem frameTransportedLaw_eq_realDensity_of_image_eq_univ {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (himage : frameGaussianTransport U r '' frameSlabInterior U r = univ) :
    frameTransportedLaw U r = euclideanDensityLaw (frameTransportRealDensity U r hr) := by
  rw [frameTransportedLaw_eq_image_density U r hr, himage, Measure.restrict_univ]
  rfl

theorem frameTransportRealDensity_integral_of_image_eq_univ {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (himage : frameGaussianTransport U r '' frameSlabInterior U r = univ)
    (hc : Continuous (frameTransportRealDensity U r hr)) :
    (∫ y, frameTransportRealDensity U r hr y) = 1 := by
  have hi := (frameTransportRealDensity_gaussianDominated_of_image_eq_univ U r hr himage).integrable hc
  have hp := frameTransportRealDensity_pos U r hr
  letI := frameTransportedLaw_isProbabilityMeasure U r hr
  have hm : (euclideanDensityLaw (frameTransportRealDensity U r hr)) univ = 1 := by
    rw [← frameTransportedLaw_eq_realDensity_of_image_eq_univ U r hr himage]
    exact measure_univ
  rw [euclideanDensityLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun y => (hp y).le))] at hm
  exact ENNReal.ofReal_eq_one.mp hm

theorem frameTransportedLaw_regular_density_of_image_open {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (himage : frameGaussianTransport U r '' frameSlabInterior U r = univ)
    (hopen : ∀ s : Set (E k), IsOpen s → s ⊆ frameSlabInterior U r →
      IsOpen (frameGaussianTransport U r '' s)) :
    ∃ f : E k → ℝ, Continuous f ∧ GaussianDominated f ∧ (∀ y, 0 < f y) ∧
      (∫ y, f y) = 1 ∧ frameTransportedLaw U r = euclideanDensityLaw f := by
  have hc := frameTransportRealDensity_continuous_of_inverse U r hr himage
    (frameGaussianInverse_continuous_of_image_open U r hr himage hopen)
  exact ⟨frameTransportRealDensity U r hr, hc,
    frameTransportRealDensity_gaussianDominated_of_image_eq_univ U r hr himage,
    frameTransportRealDensity_pos U r hr,
    frameTransportRealDensity_integral_of_image_eq_univ U r hr himage hc,
    frameTransportedLaw_eq_realDensity_of_image_eq_univ U r hr himage⟩

#print axioms frameTransportRealDensity_gaussianDominated_of_image_eq_univ
#print axioms frameTransportedLaw_regular_density_of_image_open

end CubeSections
