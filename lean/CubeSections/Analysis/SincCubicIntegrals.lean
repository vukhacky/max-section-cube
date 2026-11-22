import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Exact central-lobe sine-cubic integrals used in the quantitative p=3 bound. -/

noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubeSections

theorem integral_sin_pi_cubed :
    (∫ s in (0 : ℝ)..1, Real.sin (Real.pi * s) ^ 3) = 4 / (3 * Real.pi) := by
  rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.sin x ^ 3) Real.pi_ne_zero]
  simp only [mul_zero, mul_one, smul_eq_mul, integral_sin_pow_three,
    Real.cos_zero, Real.cos_pi]
  field_simp
  ring

private def polynomialSinePrimitive (a s : ℝ) : ℝ :=
  -(s * (1 - s) * Real.cos (a * s)) / a +
    (1 - 2 * s) * Real.sin (a * s) / a ^ 2 - 2 * Real.cos (a * s) / a ^ 3

private theorem hasDerivAt_polynomialSinePrimitive {a : ℝ} (ha : a ≠ 0) (s : ℝ) :
    HasDerivAt (polynomialSinePrimitive a) (s * (1 - s) * Real.sin (a * s)) s := by
  have hlin := (hasDerivAt_id s).const_mul a
  have hp : HasDerivAt (fun t : ℝ => t * (1 - t)) (1 - 2 * s) s := by
    convert (hasDerivAt_id s).mul ((hasDerivAt_id s).const_sub 1) using 1
    · rfl
    · simp only [id_eq]
      ring
  have hlin₂ : HasDerivAt (fun t : ℝ => 1 - 2 * t) (-2) s := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id s).const_mul 2).const_sub 1
  have h := (((hp.mul hlin.cos).neg.div_const a).add
    ((hlin₂.mul hlin.sin).div_const (a ^ 2))).sub ((hlin.cos.const_mul 2).div_const (a ^ 3))
  convert h using 1
  · rfl
  · simp only [id_eq]
    field_simp
    ring

theorem integral_polynomial_sine {a : ℝ} (ha : a ≠ 0)
    (hsin : Real.sin a = 0) (hcos : Real.cos a = -1) :
    (∫ s in (0 : ℝ)..1, s * (1 - s) * Real.sin (a * s)) = 4 / a ^ 3 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_polynomialSinePrimitive ha s)
    (show IntervalIntegrable (fun s => s * (1 - s) * Real.sin (a * s)) volume 0 1 from
      (by fun_prop : Continuous (fun s : ℝ => s * (1 - s) * Real.sin (a * s))).intervalIntegrable 0 1)]
  simp only [polynomialSinePrimitive, mul_one, mul_zero, sub_self, zero_mul,
    Real.sin_zero, Real.cos_zero, hsin, hcos, zero_div, neg_zero, zero_add, sub_zero]
  ring

theorem integral_polynomial_sin_pi_cubed :
    (∫ s in (0 : ℝ)..1, s * (1 - s) * Real.sin (Real.pi * s) ^ 3) =
      80 / (27 * Real.pi ^ 3) := by
  have hfun : (fun s : ℝ => s * (1 - s) * Real.sin (Real.pi * s) ^ 3) =
      fun s => (3 * (s * (1 - s) * Real.sin (Real.pi * s)) -
        s * (1 - s) * Real.sin ((3 * Real.pi) * s)) / 4 := by
    funext s
    have ht := Real.sin_three_mul (Real.pi * s)
    rw [show 3 * (Real.pi * s) = (3 * Real.pi) * s by ring] at ht
    rw [ht]
    ring
  rw [hfun, intervalIntegral.integral_div,
    intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun s : ℝ => 3 * (s * (1 - s) * Real.sin (Real.pi * s)))).intervalIntegrable 0 1)
      ((by fun_prop : Continuous (fun s : ℝ => s * (1 - s) * Real.sin ((3 * Real.pi) * s))).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul,
    integral_polynomial_sine Real.pi_ne_zero Real.sin_pi Real.cos_pi,
    integral_polynomial_sine (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (by norm_num [Real.sin_three_mul]) (by norm_num [Real.cos_three_mul])]
  field_simp
  ring

theorem integral_cubic_weight_majorant :
    (∫ s in (0 : ℝ)..1, Real.sin (Real.pi * s) ^ 3 * ((9 / 8 : ℝ) - 2 * s * (1 - s))) =
      3 / (2 * Real.pi) - 160 / (27 * Real.pi ^ 3) := by
  have hfun : (fun s : ℝ => Real.sin (Real.pi * s) ^ 3 * ((9 / 8 : ℝ) - 2 * s * (1 - s))) =
      fun s => (9 / 8 : ℝ) * Real.sin (Real.pi * s) ^ 3 -
        2 * (s * (1 - s) * Real.sin (Real.pi * s) ^ 3) := by
    funext s
    ring
  rw [hfun, intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun s : ℝ => (9 / 8 : ℝ) * Real.sin (Real.pi * s) ^ 3)).intervalIntegrable 0 1)
      ((by fun_prop : Continuous (fun s : ℝ => 2 * (s * (1 - s) * Real.sin (Real.pi * s) ^ 3))).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_sin_pi_cubed, integral_polynomial_sin_pi_cubed]
  ring

end CubeSections
