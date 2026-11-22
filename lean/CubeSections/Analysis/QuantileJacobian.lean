import CubeSections.Analysis.GaussianQuantile

/-! Explicit slope identities for the actual interval Gaussian transport. -/

noncomputable section
open Set ProbabilityTheory

namespace CubeSections

theorem inv_standardGaussianPDF (t : ℝ) :
    (gaussianPDFReal 0 1 t)⁻¹ = Real.sqrt (2 * Real.pi) * Real.exp (t ^ 2 / 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, mul_inv_rev, inv_inv]
  rw [← Real.exp_neg]
  have heq : -(-t ^ 2 / (2 : ℝ)) = t ^ 2 / 2 := by ring
  rw [heq]
  exact mul_comm _ _

theorem intervalGaussianTransport_slope_exp (r s : ℝ) :
    (2 * r * gaussianPDFReal 0 1 (intervalGaussianTransport r s))⁻¹ =
      (Real.sqrt (2 * Real.pi) / (2 * r)) * Real.exp (intervalGaussianTransport r s ^ 2 / 2) := by
  rw [mul_inv_rev, inv_standardGaussianPDF]
  ring

theorem intervalGaussianTransport_density_deriv {r s : ℝ}
    (hr : 0 < r) (hs : s ∈ Ioo (-r) r) :
    gaussianPDFReal 0 1 (intervalGaussianTransport r s) * deriv (intervalGaussianTransport r) s =
      (2 * r)⁻¹ := by
  rw [(hasDerivAt_intervalGaussianTransport hr hs).deriv]
  have hp := ne_of_gt (gaussianPDFReal_pos 0 1 (intervalGaussianTransport r s) (by norm_num))
  field_simp

theorem intervalGaussianTransport_log_slope (r s : ℝ) (hr : 0 < r) :
    Real.log (2 * r * gaussianPDFReal 0 1 (intervalGaussianTransport r s))⁻¹ =
      Real.log (Real.sqrt (2 * Real.pi) / (2 * r)) + intervalGaussianTransport r s ^ 2 / 2 := by
  rw [intervalGaussianTransport_slope_exp, Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]

theorem intervalGaussianTransport_surjOn {r : ℝ} (hr : 0 < r) :
    SurjOn (intervalGaussianTransport r) (Ioo (-r) r) univ := by
  intro t ht
  refine ⟨2 * r * standardGaussianCDF t - r, ?_, ?_⟩
  · have hc := standardGaussianCDF_mem_Ioo t
    constructor <;> nlinarith [mul_pos hr hc.1, mul_pos hr (sub_pos.mpr hc.2)]
  · unfold intervalGaussianTransport
    have heq : (2 * r * standardGaussianCDF t - r + r) / (2 * r) = standardGaussianCDF t := by
      field_simp
      ring
    rw [heq, standardGaussianQuantile_CDF]

theorem intervalGaussianTransport_image {r : ℝ} (hr : 0 < r) :
    intervalGaussianTransport r '' Ioo (-r) r = univ :=
  eq_univ_of_forall (fun t => intervalGaussianTransport_surjOn hr (mem_univ t))

end CubeSections
