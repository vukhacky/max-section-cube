import CubeSections.Analysis.GaussianScore
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Exact Gaussian integrals for the bounded exponential score. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CubeSections

/-- Real Gaussian integral with a linear term, by completing the square. -/
theorem integral_exp_quadratic (a b c : ℝ) (ha : 0 < a) :
    (∫ x : ℝ, Real.exp (-a * x ^ 2 + b * x + c)) =
      Real.sqrt (Real.pi / a) * Real.exp (b ^ 2 / (4 * a) + c) := by
  have hfun : (fun x : ℝ => Real.exp (-a * x ^ 2 + b * x + c)) =
      (fun x => Real.exp (-a * (x - b / (2 * a)) ^ 2) * Real.exp (b ^ 2 / (4 * a) + c)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hfun, integral_mul_const,
    integral_sub_right_eq_self (fun x : ℝ => Real.exp (-a * x ^ 2)) (b / (2 * a)),
    integral_gaussian]

private theorem gaussian_normalization_sqrt (a : ℝ) (ha : 0 < 1 + 2 * a) :
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / (a + 1 / 2)) =
      Real.sqrt (1 / (1 + 2 * a)) := by
  have ha' : 0 < a + 1 / 2 := by linarith
  have hane : 1 + a * 2 ≠ 0 := by linarith
  have hane' : 2 * a + 1 ≠ 0 := by linarith
  rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp [ne_of_gt ha, ne_of_gt ha', hane, Real.pi_ne_zero]
  all_goals try field_simp [hane']
  all_goals ring

/-- Exact Laplace transform of a quadratic under the standard one-dimensional Gaussian. -/
theorem integral_standardGaussian_quadratic (a b c : ℝ) (ha : 0 < 1 + 2 * a) :
    (∫ x : ℝ, Real.exp (-a * x ^ 2 + b * x + c) ∂(gaussianReal 0 1)) =
      Real.sqrt (1 / (1 + 2 * a)) * Real.exp (b ^ 2 / (2 * (1 + 2 * a)) + c) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have hfun : (fun x : ℝ => gaussianPDFReal 0 1 x • Real.exp (-a * x ^ 2 + b * x + c)) =
      (fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(a + 1 / 2) * x ^ 2 + b * x + c)) := by
    funext x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  rw [hfun, integral_const_mul, integral_exp_quadratic _ _ _ (by linarith)]
  rw [← mul_assoc, gaussian_normalization_sqrt a ha]
  congr 2
  field_simp
  ring

/-- The score's second moment is `sqrt(3/5)`. -/
theorem integral_gaussianScore_sq :
    (∫ x : ℝ, gaussianScore x ^ 2 ∂(gaussianReal 0 1)) = Real.sqrt (3 / 5 : ℝ) := by
  have h := integral_standardGaussian_quadratic (1 / 3 : ℝ) 0 0 (by norm_num)
  norm_num at h
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3), ← h]
  apply integral_congr_ae
  filter_upwards with x
  rw [gaussianScore_sq]
  congr 1
  ring

/-- A shifted linear score integrated against a standard Gaussian. -/
theorem integral_gaussianScore_affine (u v : ℝ) :
    (∫ y : ℝ, gaussianScore (u + v * y) ∂(gaussianReal 0 1)) =
      Real.sqrt (3 / (3 + v ^ 2)) * Real.exp (-u ^ 2 / (2 * (3 + v ^ 2))) := by
  have hv : 0 < 3 + v ^ 2 := by positivity
  have h := integral_standardGaussian_quadratic (v ^ 2 / 6) (-(u * v) / 3) (-u ^ 2 / 6)
    (by nlinarith [sq_nonneg v])
  have hfun : (fun y : ℝ => Real.exp (-(v ^ 2 / 6) * y ^ 2 + -(u * v) / 3 * y + -u ^ 2 / 6)) =
      (fun y => gaussianScore (u + v * y)) := by
    funext y
    unfold gaussianScore
    congr 1
    ring
  rw [hfun] at h
  rw [h]
  have hfrac : 1 / (1 + 2 * (v ^ 2 / 6)) = 3 / (3 + v ^ 2) := by field_simp; ring
  have hexp : (-(u * v) / 3) ^ 2 / (2 * (1 + 2 * (v ^ 2 / 6))) + -u ^ 2 / 6 =
      -u ^ 2 / (2 * (3 + v ^ 2)) := by field_simp; ring
  rw [hfrac, hexp]

end CubeSections
