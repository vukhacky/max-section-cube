import CubeSections.Analysis.TransportDensity
import CubeSections.Analysis.FrameQuantileMoments
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-! Actual inverse lifting of a coupling of the transported law and a Gaussian.
This file proves the lifting and moment facts; existence of a low-cost coupling
is a separate theorem. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory

namespace CubeSections

theorem frameGaussianInverse_map_law {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    (frameTransportedLaw U r).map (frameGaussianInverse U r hr) = frameSlabUniform U r := by
  rw [frameTransportedLaw, Measure.map_map (measurable_frameGaussianInverse U r hr)
    (measurable_frameGaussianTransport U r)]
  have heq : (frameGaussianInverse U r hr ∘ frameGaussianTransport U r) =ᵐ[frameSlabUniform U r] id := by
    filter_upwards [frameSlabUniform_ae_mem U r] with x hx
    exact frameGaussianInverse_transport U r hr hx
  rw [Measure.map_congr heq, Measure.map_id]

theorem frameGaussianTransport_inverse_ae {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    ∀ᵐ y ∂frameTransportedLaw U r,
      frameGaussianTransport U r (frameGaussianInverse U r hr y) = y := by
  apply (ae_map_iff (measurable_frameGaussianTransport U r).aemeasurable
    (measurableSet_eq_fun ((measurable_frameGaussianTransport U r).comp
      (measurable_frameGaussianInverse U r hr)) measurable_id)).mpr
  filter_upwards [frameSlabUniform_ae_mem U r] with x hx
  simp only [Function.comp_def, id_eq]
  rw [frameGaussianInverse_transport U r hr hx]

theorem integrable_norm_sq_frameTransportedLaw {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    Integrable (fun y : E k => ‖y‖ ^ 2) (frameTransportedLaw U r) :=
  (integrable_map_measure (by fun_prop) (measurable_frameGaussianTransport U r).aemeasurable).mpr
    (integrable_frameGaussianTransport_sq U r hr)

theorem memLp_id_frameTransportedLaw_two {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : MemLp id 2 (frameTransportedLaw U r) :=
  (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr (integrable_norm_sq_frameTransportedLaw U r hr)

theorem integrable_norm_sq_stdGaussian (k : ℕ) :
    Integrable (fun y : E k => ‖y‖ ^ 2) (stdGaussian (E k)) :=
  (memLp_two_iff_integrable_sq_norm (by fun_prop)).mp
    (IsGaussian.memLp_two_id (μ := stdGaussian (E k)))

theorem integrable_joint_quadratic_cost {k : ℕ} (π : Measure (E k × E k))
    (ν₀ ν₁ : Measure (E k)) (h₀ : π.map Prod.fst = ν₀) (h₁ : π.map Prod.snd = ν₁)
    (hI₀ : Integrable (fun x : E k => ‖x‖ ^ 2) ν₀)
    (hI₁ : Integrable (fun x : E k => ‖x‖ ^ 2) ν₁) :
    Integrable (fun p : E k × E k => ‖p.1 - p.2‖ ^ 2) π := by
  have hfst : Integrable (fun p : E k × E k => ‖p.1‖ ^ 2) π := by
    rw [← h₀] at hI₀
    exact hI₀.comp_measurable measurable_fst
  have hsnd : Integrable (fun p : E k × E k => ‖p.2‖ ^ 2) π := by
    rw [← h₁] at hI₁
    exact hI₁.comp_measurable measurable_snd
  apply ((hfst.add hsnd).const_mul 2).mono' (by fun_prop)
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ‖p.1 - p.2‖ ^ 2 ≤ 2 * (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2)
  have h := sq_le_sq₀ (norm_nonneg (p.1 - p.2)) (add_nonneg (norm_nonneg p.1) (norm_nonneg p.2))
  have hb := h.mpr (norm_sub_le p.1 p.2)
  nlinarith [sq_nonneg (‖p.1‖ - ‖p.2‖)]

/-- Pull a coupling of `F(X)` and `G` back to a coupling of `X` and `G`. -/
def framePullbackCoupling {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (π : Measure (E k × E k)) : Measure (E k × E k) :=
  π.map (fun p => (frameGaussianInverse U r hr p.1, p.2))

theorem framePullbackCoupling_isProbabilityMeasure {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (π : Measure (E k × E k)) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (framePullbackCoupling U r hr π) := by
  unfold framePullbackCoupling
  infer_instance

theorem framePullbackCoupling_fst {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (π : Measure (E k × E k))
    (hπ : π.map Prod.fst = frameTransportedLaw U r) :
    (framePullbackCoupling U r hr π).map Prod.fst = frameSlabUniform U r := by
  rw [framePullbackCoupling, Measure.map_map measurable_fst (by fun_prop)]
  change π.map (frameGaussianInverse U r hr ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_frameGaussianInverse U r hr) measurable_fst, hπ,
    frameGaussianInverse_map_law U r hr]

theorem framePullbackCoupling_snd {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (π : Measure (E k × E k)) :
    (framePullbackCoupling U r hr π).map Prod.snd = π.map Prod.snd := by
  rw [framePullbackCoupling, Measure.map_map measurable_snd (by fun_prop)]
  rfl

theorem framePullbackCoupling_cost {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (π : Measure (E k × E k))
    (hπ : π.map Prod.fst = frameTransportedLaw U r) :
    (∫ p, ‖frameGaussianTransport U r p.1 - p.2‖ ^ 2 ∂framePullbackCoupling U r hr π) =
      ∫ p, ‖p.1 - p.2‖ ^ 2 ∂π := by
  have h := frameGaussianTransport_inverse_ae U r hr
  rw [← hπ] at h
  have hfst := ae_of_ae_map measurable_fst.aemeasurable h
  rw [framePullbackCoupling, integral_map (by fun_prop) (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [hfst] with p hp
  simp only [hp]

theorem integrable_framePullbackCoupling_cost {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (π : Measure (E k × E k))
    (hπ : π.map Prod.fst = frameTransportedLaw U r)
    (hG : π.map Prod.snd = stdGaussian (E k)) :
    Integrable (fun p => ‖frameGaussianTransport U r p.1 - p.2‖ ^ 2) (framePullbackCoupling U r hr π) := by
  have hi := integrable_joint_quadratic_cost π _ _ hπ hG
    (integrable_norm_sq_frameTransportedLaw U r hr) (integrable_norm_sq_stdGaussian k)
  have h := frameGaussianTransport_inverse_ae U r hr
  rw [← hπ] at h
  have hfst := ae_of_ae_map measurable_fst.aemeasurable h
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  apply hi.congr
  filter_upwards [hfst] with p hp
  simp only [Function.comp_def, hp]

end CubeSections
