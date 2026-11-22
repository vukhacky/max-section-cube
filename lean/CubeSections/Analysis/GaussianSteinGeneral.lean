import CubeSections.Analysis.GaussianStein

/-! Gaussian integration by parts under explicit Gaussian integrability, without
compact-support or boundary-value assumptions. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CubeSections

theorem integrable_standardGaussian_density_iff (g : ℝ → ℝ) :
    Integrable g (gaussianReal 0 1) ↔ Integrable (fun t => gaussianPDFReal 0 1 t * g t) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simpa only [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _), smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' (g := g) (measurable_gaussianPDF 0 1)
      (ae_of_all _ (fun t => gaussianPDF_lt_top (μ := 0) (v := 1) (x := t))))

/-- Stein's identity with all tail hypotheses stated as ordinary Gaussian
integrability. The full-line integration-by-parts theorem proves the vanishing
boundary terms from these inputs. -/
theorem gaussian_stein_of_integrable {h h' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt h (h' x) x)
    (hI : Integrable h (gaussianReal 0 1)) (hI' : Integrable h' (gaussianReal 0 1))
    (hxI : Integrable (fun x => x * h x) (gaussianReal 0 1)) :
    (∫ x, h' x ∂gaussianReal 0 1) = ∫ x, x * h x ∂gaussianReal 0 1 := by
  have hi₀ : Integrable (fun x => h x * gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using (integrable_standardGaussian_density_iff h).mp hI
  have hi₁ : Integrable (fun x => h x * (-x * gaussianPDFReal 0 1 x)) := by
    apply ((integrable_standardGaussian_density_iff (fun x => x * h x)).mp hxI).neg.congr
    filter_upwards with x
    simp only [Pi.neg_apply]
    ring
  have hi₂ : Integrable (fun x => h' x * gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using (integrable_standardGaussian_density_iff h').mp hI'
  have hIBP := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := h) (v := gaussianPDFReal 0 1) (u' := h')
    (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => hd x) (fun x _ => hasDerivAt_standardGaussianPDF x) hi₁ hi₂ hi₀
  have hleft : (∫ x, h x * (-x * gaussianPDFReal 0 1 x)) =
      -(∫ x, gaussianPDFReal 0 1 x * (x * h x)) := by
    rw [← integral_neg]
    congr 1
    funext x
    ring
  have hright : (∫ x, h' x * gaussianPDFReal 0 1 x) =
      ∫ x, gaussianPDFReal 0 1 x * h' x := by
    congr 1
    funext x
    ring
  rw [hleft, hright] at hIBP
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  linarith

end CubeSections
