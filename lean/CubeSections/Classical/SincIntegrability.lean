import CubeSections.Classical.BallScalarReduction
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Integrability and positivity of the manuscript's real sinc powers. -/
noncomputable section
open MeasureTheory

namespace CubeSections

theorem sinc_sq_le_cauchy (x : ℝ) :
    Real.sinc x ^ 2 ≤ 2/(1+x^2) := by
  have hden : 0 < 1+x^2 := by positivity
  apply (le_div_iff₀ hden).2
  have hnorm : Real.sinc x ^ 2 ≤ 1 := by
    have h := (sq_le_sq₀ (abs_nonneg (Real.sinc x)) (by norm_num : (0 : ℝ) ≤ 1)).2
      (Real.abs_sinc_le_one x)
    simpa only [sq_abs, one_pow] using h
  have hsin : Real.sin x ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (Real.cos x)]
  have hmul : x*Real.sinc x = Real.sin x := by
    by_cases hx : x=0
    · simp [hx]
    · rw [Real.sinc_of_ne_zero hx]
      field_simp
  have hsq : x^2 * Real.sinc x^2 = Real.sin x^2 := by
    calc
      x^2 * Real.sinc x^2 = (x*Real.sinc x)^2 := (mul_pow _ _ _).symm
      _ = _ := by rw [hmul]
  nlinarith

theorem ballSincIntegrand_le_cauchy (p t : ℝ) (hp : 2 ≤ p) :
    ballSincIntegrand p t ≤ 2/(1+(Real.pi*t)^2) := by
  calc
    ballSincIntegrand p t ≤ |Real.sinc (Real.pi*t)| ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg _) (Real.abs_sinc_le_one _)
        (by norm_num) hp
    _ = Real.sinc (Real.pi*t)^2 := by rw [Real.rpow_two, sq_abs]
    _ ≤ _ := sinc_sq_le_cauchy _

theorem integrable_ballSincIntegrand (p : ℝ) (hp : 2 ≤ p) :
    Integrable (ballSincIntegrand p) := by
  have hC : Integrable (fun t : ℝ => 2/(1+(Real.pi*t)^2)) := by
    simpa only [div_eq_mul_inv] using
      (integrable_inv_one_add_sq.comp_mul_left' Real.pi_ne_zero).const_mul 2
  apply hC.mono' (continuous_ballSincIntegrand p (by linarith)).aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (ballSincIntegrand_nonneg p t)]
    exact ballSincIntegrand_le_cauchy p t hp)

theorem ballSincIntegral_pos_of_two_le (p : ℝ) (hp : 2 ≤ p) :
    0 < ballSincIntegral p :=
  ballSincIntegral_pos p (by linarith) (integrable_ballSincIntegrand p hp)

/-- A coarse sinc-power bound establishing integrability independently of the
sharp scalar inequality. -/
theorem ballSincIntegral_le_two (p : ℝ) (hp : 2 ≤ p) : ballSincIntegral p ≤ 2 := by
  have hC : Integrable (fun t : ℝ => 2/(1+(Real.pi*t)^2)) := by
    simpa only [div_eq_mul_inv] using
      (integrable_inv_one_add_sq.comp_mul_left' Real.pi_ne_zero).const_mul 2
  have h := integral_mono (integrable_ballSincIntegrand p hp) hC
    (fun t => ballSincIntegrand_le_cauchy p t hp)
  have hval : (∫ t : ℝ, 2/(1+(Real.pi*t)^2)) = 2 := by
    simp only [div_eq_mul_inv]
    rw [integral_const_mul, Measure.integral_comp_mul_left (fun x : ℝ => (1+x^2)⁻¹) Real.pi,
      integral_univ_inv_one_add_sq, smul_eq_mul, abs_of_pos (inv_pos.2 Real.pi_pos)]
    field_simp
  exact h.trans_eq hval

theorem strictBallSincBound_of_sharp_bounds
    (h : ∀ p : ℝ, 2 ≤ p → ballSincIntegral p ≤ Real.sqrt (2/p) ∧
      (ballSincIntegral p = Real.sqrt (2/p) ↔ p=2)) : StrictBallSincBound := by
  intro p hp
  exact ⟨integrable_ballSincIntegrand p hp, h p hp⟩

#print axioms integrable_ballSincIntegrand
#print axioms ballSincIntegral_pos_of_two_le
#print axioms ballSincIntegral_le_two
end CubeSections
