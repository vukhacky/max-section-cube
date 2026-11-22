import CubeSections.Analysis.PositiveDensityTransport
import CubeSections.Analysis.TransportDensity
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Endpoint behavior and the actual probability pushforward of the positive
density Gaussian quantile transport. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped NNReal ENNReal Topology

namespace CubeSections

def positiveDensityLaw (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (f x))

theorem positiveDensityLaw_isProbabilityMeasure {f : ℝ → ℝ} (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) : IsProbabilityMeasure (positiveDensityLaw f) := by
  constructor
  rw [positiveDensityLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun x => (hp x).le)), hm]
  norm_num

theorem densityCDF_eq_cdf {f : ℝ → ℝ} (hi : Integrable f) (hp : ∀ x, 0 < f x)
    (hm : (∫ x, f x) = 1) (x : ℝ) : densityCDF f x = cdf (positiveDensityLaw f) x := by
  letI := positiveDensityLaw_isProbabilityMeasure hi hp hm
  rw [cdf_eq_real, measureReal_def, positiveDensityLaw, withDensity_apply _ measurableSet_Iic,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ (fun t => (hp t).le)),
    ENNReal.toReal_ofReal (integral_nonneg (fun t => (hp t).le))]
  rfl

theorem tendsto_densityCDF_atBot {f : ℝ → ℝ} (hi : Integrable f) (hp : ∀ x, 0 < f x)
    (hm : (∫ x, f x) = 1) : Tendsto (densityCDF f) atBot (𝓝 0) := by
  have heq : densityCDF f = cdf (positiveDensityLaw f) := funext (densityCDF_eq_cdf hi hp hm)
  rw [heq]
  exact tendsto_cdf_atBot _

theorem tendsto_densityCDF_atTop {f : ℝ → ℝ} (hi : Integrable f) (hp : ∀ x, 0 < f x)
    (hm : (∫ x, f x) = 1) : Tendsto (densityCDF f) atTop (𝓝 1) := by
  have heq : densityCDF f = cdf (positiveDensityLaw f) := funext (densityCDF_eq_cdf hi hp hm)
  rw [heq]
  exact tendsto_cdf_atTop _

theorem densityCDF_surjOn {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) : SurjOn (densityCDF f) univ (Ioo (0 : ℝ) 1) := by
  intro p hpI
  have hlo : ∃ x : ℝ, densityCDF f x < p :=
    ((tendsto_densityCDF_atBot hi hp hm).eventually (eventually_lt_nhds hpI.1)).exists
  have hhi : ∃ x : ℝ, p < densityCDF f x :=
    ((tendsto_densityCDF_atTop hi hp hm).eventually (eventually_gt_nhds hpI.2)).exists
  obtain ⟨x, hx⟩ := mem_range_of_exists_le_of_exists_ge (continuous_densityCDF hc hi)
    (hlo.imp fun _ h => h.le) (hhi.imp fun _ h => h.le)
  exact ⟨x, mem_univ _, hx⟩

theorem densityGaussianTransport_surjective {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) : Function.Surjective (densityGaussianTransport f) := by
  intro y
  obtain ⟨x, _, hx⟩ := densityCDF_surjOn hc hi hp hm (standardGaussianCDF_mem_Ioo y)
  refine ⟨x, ?_⟩
  rw [densityGaussianTransport, hx, standardGaussianQuantile_CDF]

theorem densityGaussianTransport_map_jacobian {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) :
    (volume.withDensity (fun x => ENNReal.ofReal (densityGaussianSlope f x))).map
      (densityGaussianTransport f) = volume := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar volume
    (s := (univ : Set ℝ)) (MeasurableSet.univ : MeasurableSet (univ : Set ℝ)).nullMeasurableSet
    (fun x _ => (hasDerivAt_densityGaussianTransport hc hi hp hm x).hasDerivWithinAt.hasFDerivWithinAt)
    (strictMono_densityGaussianTransport hc hi hp hm).injective.injOn
  simpa only [Measure.restrict_univ, image_univ, (densityGaussianTransport_surjective hc hi hp hm).range_eq,
    det_toSpanSingleton, abs_of_pos (densityGaussianSlope_pos hp _)] using h

/-- The constructed scalar quantile sends the actual density measure to the
actual standard Gaussian, with no distributional premise. -/
theorem densityGaussianTransport_map_law {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) :
    (positiveDensityLaw f).map (densityGaussianTransport f) = gaussianReal 0 1 := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    ← densityGaussianTransport_map_jacobian hc hi hp hm,
    ← map_withDensity_comp_eq _ _ (measurable_densityGaussianTransport hc hi hp hm) _
      (measurable_gaussianPDF 0 1)]
  congr 1
  have hmul := withDensity_mul volume (measurable_densityGaussianSlope hc hi hp hm).ennreal_ofReal
    ((measurable_gaussianPDF 0 1).comp (measurable_densityGaussianTransport hc hi hp hm))
  simp only [Function.comp_def] at hmul
  rw [← hmul]
  apply withDensity_congr_ae
  filter_upwards with x
  change ENNReal.ofReal (f x) = ENNReal.ofReal (densityGaussianSlope f x) *
    gaussianPDF 0 1 (densityGaussianTransport f x)
  rw [gaussianPDF_def, ← ENNReal.ofReal_mul (densityGaussianSlope_pos hp x).le]
  congr 1
  rw [mul_comm, densityGaussianTransport_density_jacobian]

theorem densityGaussianTransport_measurePreserving {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) :
    MeasurePreserving (densityGaussianTransport f) (positiveDensityLaw f) (gaussianReal 0 1) :=
  ⟨measurable_densityGaussianTransport hc hi hp hm, densityGaussianTransport_map_law hc hi hp hm⟩

end CubeSections
