import CubeSections.Analysis.QuantileJacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Exact pushforward integrals and finite moments of the scalar interval quantile. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CubeSections

private theorem quantile_change_integrand (r s : ℝ) (hr : 0 < r) (g : ℝ → ℝ) :
    |(2 * r * gaussianPDFReal 0 1 (intervalGaussianTransport r s))⁻¹| *
        (gaussianPDFReal 0 1 (intervalGaussianTransport r s) * g (intervalGaussianTransport r s)) =
      (2 * r)⁻¹ * g (intervalGaussianTransport r s) := by
  have hp := gaussianPDFReal_pos 0 1 (intervalGaussianTransport r s) (by norm_num)
  rw [abs_of_pos (inv_pos.mpr (mul_pos (by positivity) hp))]
  field_simp

theorem integral_intervalGaussianTransport (r : ℝ) (hr : 0 < r) (g : ℝ → ℝ) :
    (∫ s in Ioo (-r) r, g (intervalGaussianTransport r s)) =
      2 * r * ∫ t, g t ∂gaussianReal 0 1 := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun s hs => (hasDerivAt_intervalGaussianTransport hr hs).hasDerivWithinAt)
    (strictMonoOn_intervalGaussianTransport hr).injOn
    (fun t => gaussianPDFReal 0 1 t * g t)
  simp only [intervalGaussianTransport_image hr, Measure.restrict_univ] at h
  simp only [smul_eq_mul, quantile_change_integrand r _ hr g] at h
  rw [integral_const_mul] at h
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  rw [h]
  field_simp

private theorem integrable_gaussian_density_iff (g : ℝ → ℝ) :
    Integrable g (gaussianReal 0 1) ↔ Integrable (fun t => gaussianPDFReal 0 1 t * g t) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simpa only [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _), smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' (g := g) (measurable_gaussianPDF 0 1)
      (ae_of_all _ (fun t => gaussianPDF_lt_top (μ := 0) (v := 1) (x := t))))

theorem integrable_intervalGaussianTransport_iff (r : ℝ) (hr : 0 < r) (g : ℝ → ℝ) :
    IntegrableOn (fun s => g (intervalGaussianTransport r s)) (Ioo (-r) r) ↔
      Integrable g (gaussianReal 0 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun s hs => (hasDerivAt_intervalGaussianTransport hr hs).hasDerivWithinAt)
    (strictMonoOn_intervalGaussianTransport hr).injOn
    (fun t => gaussianPDFReal 0 1 t * g t)
  rw [intervalGaussianTransport_image hr, integrableOn_univ] at h
  simp only [smul_eq_mul, quantile_change_integrand r _ hr g] at h
  rw [integrable_gaussian_density_iff]
  rw [h]
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (by positivity : (2 * r)⁻¹ ≠ 0)) _).symm

theorem integrableOn_intervalGaussianTransport_sq (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun s => intervalGaussianTransport r s ^ 2) (Ioo (-r) r) := by
  apply (integrable_intervalGaussianTransport_iff r hr (fun t => t ^ 2)).mpr
  simpa only [id_eq] using (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq

theorem integral_intervalGaussianTransport_sq (r : ℝ) (hr : 0 < r) :
    (∫ s in Ioo (-r) r, intervalGaussianTransport r s ^ 2) = 2 * r := by
  rw [integral_intervalGaussianTransport r hr (fun t => t ^ 2)]
  have hv := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id.aemeasurable] at hv
  change (∫ t : ℝ, (t - ∫ t : ℝ, t ∂gaussianReal 0 1) ^ 2 ∂gaussianReal 0 1) = (1 : ℝ) at hv
  simp only [integral_id_gaussianReal, sub_zero, NNReal.coe_one] at hv
  rw [hv, mul_one]

end CubeSections
