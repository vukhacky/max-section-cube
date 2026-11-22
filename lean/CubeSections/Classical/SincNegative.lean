import CubeSections.Classical.BallThree
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Integrability and evenness for the negative part of the signed cubic sinc
integrand. This module supplies exact measure-theoretic interfaces for the
independent negative-lobe estimate. -/
noncomputable section
open Set MeasureTheory
namespace CubeSections

theorem integrable_sinc_cube : Integrable (fun t : ℝ => Real.sinc (Real.pi*t)^3) := by
  apply (integrable_absSinc_pow 3 (by norm_num)).mono'
    (by fun_prop : AEStronglyMeasurable (fun t : ℝ => Real.sinc (Real.pi*t)^3) volume)
  exact ae_of_all _ (fun t => by rw [Real.norm_eq_abs, ← pow_abs])

theorem integrable_sinc_negative_cube :
    Integrable (fun t : ℝ => max (-(Real.sinc (Real.pi*t))^3) 0) := by
  apply (integrable_absSinc_pow 3 (by norm_num)).mono'
    (by fun_prop : AEStronglyMeasurable (fun t : ℝ => max (-(Real.sinc (Real.pi*t))^3) 0) volume)
  exact ae_of_all _ (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · rw [pow_abs]
      exact neg_le_abs _
    · exact pow_nonneg (abs_nonneg _) _)

theorem sinc_negative_cube_even :
    Function.Even (fun t : ℝ => max (-(Real.sinc (Real.pi*t))^3) 0) := by
  intro t
  simp only [mul_neg, Real.sinc_neg]

theorem sinc_negative_cube_integral_eq_two_half :
    (∫ t : ℝ, max (-(Real.sinc (Real.pi*t))^3) 0) =
      2 * (∫ t in Ioi (0 : ℝ), max (-(Real.sinc (Real.pi*t))^3) 0) := by
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ))
    integrable_sinc_negative_cube.integrableOn integrable_sinc_negative_cube.integrableOn
  have hneg := integral_comp_neg_Ioi (0 : ℝ)
    (fun t : ℝ => max (-(Real.sinc (Real.pi*t))^3) 0)
  simp only [neg_zero, mul_neg, Real.sinc_neg] at hneg
  rw [← hsplit, ← hneg]
  ring

theorem ballSincIntegral_three_eq_signed_add_negative :
    ballSincIntegral 3 = (∫ t : ℝ, Real.sinc (Real.pi*t)^3) +
      4 * (∫ t in Ioi (0 : ℝ), max (-(Real.sinc (Real.pi*t))^3) 0) := by
  have h := integral_abs_eq_two_mul_integral_negPart_add_integral integrable_sinc_cube
  simp only [← pow_abs, negPart_def] at h
  rw [integral_absSinc_pow, sinc_negative_cube_integral_eq_two_half] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

#print axioms integrable_sinc_negative_cube
#print axioms ballSincIntegral_three_eq_signed_add_negative
end CubeSections
