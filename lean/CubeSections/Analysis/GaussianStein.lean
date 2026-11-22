import CubeSections.Analysis.GaussianQuantile
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Gaussian integration by parts for actual compactly supported C1 functions. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff NNReal

namespace CubeSections

theorem hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := (((((hasDerivAt_id x).pow 2).neg.div_const 2).exp).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹)
  convert h using 1 <;>
    simp only [gaussianPDFReal_def, NNReal.coe_one, sub_zero, mul_one,
      Pi.neg_apply, Pi.pow_apply, id_eq] <;> norm_num <;> ring

theorem integrable_gaussian_compact_deriv {h : ℝ → ℝ} (hc : ContDiff ℝ 1 h)
    (hs : HasCompactSupport h) : Integrable (deriv h) (gaussianReal 0 1) :=
  hc.continuous_deriv_one.integrable_of_hasCompactSupport hs.deriv

theorem integrable_gaussian_compact_mul_id {h : ℝ → ℝ} (hc : Continuous h)
    (hs : HasCompactSupport h) : Integrable (fun x => x * h x) (gaussianReal 0 1) :=
  (continuous_id.mul hc).integrable_of_hasCompactSupport hs.mul_left

/-- Stein's identity for the actual standard Gaussian probability measure. -/
theorem gaussian_stein_compact {h : ℝ → ℝ} (hc : ContDiff ℝ 1 h)
    (hs : HasCompactSupport h) :
    (∫ x, deriv h x ∂gaussianReal 0 1) = ∫ x, x * h x ∂gaussianReal 0 1 := by
  have hi₀ : Integrable (fun x => h x * gaussianPDFReal 0 1 x) :=
    (hc.continuous.mul continuous_standardGaussianPDF).integrable_of_hasCompactSupport hs.mul_right
  have hi₁ : Integrable (fun x => h x * (-x * gaussianPDFReal 0 1 x)) :=
    (hc.continuous.mul (continuous_id.neg.mul continuous_standardGaussianPDF)).integrable_of_hasCompactSupport
      hs.mul_right
  have hi₂ : Integrable (fun x => deriv h x * gaussianPDFReal 0 1 x) :=
    (hc.continuous_deriv_one.mul continuous_standardGaussianPDF).integrable_of_hasCompactSupport
      hs.deriv.mul_right
  have hIBP := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := h) (v := gaussianPDFReal 0 1) (u' := deriv h)
    (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => (hc.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => hasDerivAt_standardGaussianPDF x) hi₁ hi₂ hi₀
  have hleft : (∫ x, h x * (-x * gaussianPDFReal 0 1 x)) =
      -(∫ x, gaussianPDFReal 0 1 x * (x * h x)) := by
    rw [← integral_neg]
    congr 1
    funext x
    ring
  have hright : (∫ x, deriv h x * gaussianPDFReal 0 1 x) =
      ∫ x, gaussianPDFReal 0 1 x * deriv h x := by
    congr 1
    funext x
    ring
  rw [hleft, hright] at hIBP
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  linarith

end CubeSections
