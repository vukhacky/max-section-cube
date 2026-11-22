import CubeSections.Classical.SincIntegrability
import CubeSections.Analysis.SincGaussianEnvelope
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Strict Ball's sinc estimate for every real exponent p≥4. The proof uses
the proved sinc Gaussian envelope on the first lobe, an exact two-sided power
tail integral, and rational bounds for the remaining constants.
-/
noncomputable section
open MeasureTheory Set

namespace CubeSections

def ballGaussianMajorant (p t : ℝ) : ℝ :=
  Real.exp (-(Real.pi^2*p/6)*t^2)

def ballPositiveTail (p t : ℝ) : ℝ :=
  (Ioi (1 : ℝ)).indicator (fun x : ℝ => Real.pi^(-p)*x^(-p)) t

theorem ballPositiveTail_nonneg (p t : ℝ) : 0 ≤ ballPositiveTail p t := by
  by_cases ht : t ∈ Ioi (1 : ℝ)
  · rw [ballPositiveTail, indicator_of_mem ht]
    exact mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
      (Real.rpow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) (mem_Ioi.mp ht).le) _)
  · simp [ballPositiveTail, ht]

theorem integrable_ballPositiveTail (p : ℝ) (hp : 1 < p) : Integrable (ballPositiveTail p) := by
  have h : IntegrableOn (fun x : ℝ => Real.pi^(-p)*x^(-p)) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul (Real.pi^(-p))
  exact h.integrable_indicator measurableSet_Ioi

theorem integral_ballPositiveTail (p : ℝ) (hp : 1 < p) :
    (∫ t, ballPositiveTail p t) = Real.pi^(-p)/(p-1) := by
  change (∫ t : ℝ, (Ioi (1 : ℝ)).indicator (fun x : ℝ => Real.pi^(-p)*x^(-p)) t) = _
  rw [integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith : -p < -1) (by norm_num : (0 : ℝ) < 1)]
  rw [Real.one_rpow]
  have hne : 1-p ≠ 0 := by linarith
  have hne' : p-1 ≠ 0 := by linarith
  have hne'' : -p+1 ≠ 0 := by linarith
  field_simp [hne, hne', hne'']
  <;> ring

theorem integrable_ballPositiveTail_neg (p : ℝ) (hp : 1 < p) :
    Integrable (fun t : ℝ => ballPositiveTail p (-t)) := by
  simpa only [neg_one_mul] using
    (integrable_ballPositiveTail p hp).comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0)

theorem integral_ballPositiveTail_neg (p : ℝ) (hp : 1 < p) :
    (∫ t : ℝ, ballPositiveTail p (-t)) = Real.pi^(-p)/(p-1) := by
  have h := Measure.integral_comp_mul_left (ballPositiveTail p) (-1 : ℝ)
  simpa only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul,
    integral_ballPositiveTail p hp] using h

theorem integrable_ballGaussianMajorant (p : ℝ) (hp : 0 < p) :
    Integrable (ballGaussianMajorant p) := by
  exact integrable_exp_neg_mul_sq (by positivity : 0 < Real.pi^2*p/6)

theorem integral_ballGaussianMajorant (p : ℝ) (hp : 0 < p) :
    (∫ t, ballGaussianMajorant p t) = Real.sqrt (6/(Real.pi*p)) := by
  change (∫ t : ℝ, Real.exp (-(Real.pi^2*p/6)*t^2)) = _
  rw [integral_gaussian]
  congr 1
  field_simp
  <;> ring

theorem ballSincIntegrand_le_gaussian_core (p t : ℝ) (hp : 0 ≤ p) (ht : |t| ≤ 1) :
    ballSincIntegrand p t ≤ ballGaussianMajorant p t := by
  have hpi : |Real.pi*t| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht Real.pi_pos.le
  have h := Real.rpow_le_rpow (abs_nonneg (Real.sinc (Real.pi*t)))
    (sinc_gaussian_envelope (Real.pi*t) hpi) hp
  unfold ballSincIntegrand ballGaussianMajorant
  convert h using 1
  rw [← Real.exp_mul]
  congr 1
  ring

theorem ballSincIntegrand_le_power_tail (p t : ℝ) (hp : 0 ≤ p) (ht : 1 < |t|) :
    ballSincIntegrand p t ≤ Real.pi^(-p)*|t|^(-p) := by
  have ht0 : t ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
  have hden : 0 < Real.pi*|t| := mul_pos Real.pi_pos (by linarith)
  have hs : |Real.sinc (Real.pi*t)| ≤ 1/(Real.pi*|t|) := by
    rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero ht0), abs_div,
      abs_mul, abs_of_pos Real.pi_pos]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hden.le
  calc
    ballSincIntegrand p t ≤ (1/(Real.pi*|t|))^p :=
      Real.rpow_le_rpow (abs_nonneg _) hs hp
    _ = Real.pi^(-p)*|t|^(-p) := by
      rw [one_div, ← Real.rpow_neg_eq_inv_rpow, Real.mul_rpow Real.pi_pos.le (abs_nonneg t)]

theorem ballSincIntegrand_le_gaussian_add_tails (p t : ℝ) (hp : 0 ≤ p) :
    ballSincIntegrand p t ≤
      ballGaussianMajorant p t + ballPositiveTail p t + ballPositiveTail p (-t) := by
  have hG : 0 ≤ ballGaussianMajorant p t := (Real.exp_pos _).le
  have hT := ballPositiveTail_nonneg p t
  have hN := ballPositiveTail_nonneg p (-t)
  by_cases ht : |t| ≤ 1
  · have h := ballSincIntegrand_le_gaussian_core p t hp ht
    linarith
  · have habs : 1 < |t| := lt_of_not_ge ht
    have h := ballSincIntegrand_le_power_tail p t hp habs
    rcases le_total 0 t with hsign | hsign
    · rw [abs_of_nonneg hsign] at h habs
      have heq : ballPositiveTail p t = Real.pi^(-p)*t^(-p) :=
        indicator_of_mem habs _
      rw [← heq] at h
      linarith
    · rw [abs_of_nonpos hsign] at h habs
      have heq : ballPositiveTail p (-t) = Real.pi^(-p)*(-t)^(-p) :=
        indicator_of_mem habs _
      rw [← heq] at h
      linarith

/-- The explicit Gaussian-plus-tail upper bound, independent of Ball's theorem. -/
theorem ballSincIntegral_le_gaussian_add_tail (p : ℝ) (hp : 2 ≤ p) :
    ballSincIntegral p ≤ Real.sqrt (6/(Real.pi*p)) + 2*Real.pi^(-p)/(p-1) := by
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hG := integrable_ballGaussianMajorant p hp0
  have hT := integrable_ballPositiveTail p hp1
  have hN := integrable_ballPositiveTail_neg p hp1
  have h := integral_mono (integrable_ballSincIntegrand p hp) ((hG.add hT).add hN)
    (fun t => ballSincIntegrand_le_gaussian_add_tails p t hp0.le)
  calc
    ballSincIntegral p ≤ ∫ x, ballGaussianMajorant p x + ballPositiveTail p x +
        ballPositiveTail p (-x) := h
    _ = (∫ x, ballGaussianMajorant p x + ballPositiveTail p x) +
        ∫ x, ballPositiveTail p (-x) := integral_add (hG.add hT) hN
    _ = ((∫ x, ballGaussianMajorant p x) + ∫ x, ballPositiveTail p x) +
        ∫ x, ballPositiveTail p (-x) := by rw [integral_add hG hT]
    _ = Real.sqrt (6/(Real.pi*p)) + 2*Real.pi^(-p)/(p-1) := by
      rw [integral_ballGaussianMajorant p hp0, integral_ballPositiveTail p hp1,
        integral_ballPositiveTail_neg p hp1]
      ring

theorem sqrt_div_sub_one_le_two_thirds (p : ℝ) (hp : 4 ≤ p) :
    Real.sqrt p/(p-1) ≤ (2/3 : ℝ) := by
  apply (div_le_iff₀ (by linarith : 0 < p-1)).2
  apply (sq_le_sq₀ (Real.sqrt_nonneg p) (by linarith : 0 ≤ (2/3 : ℝ)*(p-1))).1
  rw [Real.sq_sqrt (by linarith : 0 ≤ p)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (by linarith : 0 ≤ 4*p-1)]

theorem scaled_ball_tail_lt_one_fiftieth (p : ℝ) (hp : 4 ≤ p) :
    (2*Real.pi^(-p)/(p-1))*Real.sqrt p < (1/50 : ℝ) := by
  have hpi1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hp0 : 0 ≤ p := by linarith
  have hpow : Real.pi^(-p) ≤ (Real.pi^4)⁻¹ := by
    have h := Real.rpow_le_rpow_of_exponent_le hpi1 (show -p ≤ (-4 : ℝ) by linarith)
    simpa only [Real.rpow_neg Real.pi_pos.le, Real.rpow_ofNat] using h
  have hs := sqrt_div_sub_one_le_two_thirds p hp
  have hpi4 : (81 : ℝ) ≤ Real.pi^4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) Real.pi_gt_three.le 4
    norm_num at h
    exact h
  calc
    (2*Real.pi^(-p)/(p-1))*Real.sqrt p =
        (2*Real.pi^(-p))*(Real.sqrt p/(p-1)) := by ring
    _ ≤ (2*(Real.pi^4)⁻¹)*(2/3) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num)) hs
        (div_nonneg (Real.sqrt_nonneg p) (by linarith)) (by positivity)
    _ = 4/(3*Real.pi^4) := by ring
    _ < 1/50 := by
      apply (div_lt_iff₀ (by positivity : 0 < 3*Real.pi^4)).2
      nlinarith

theorem ball_gaussian_tail_lt_sharp (p : ℝ) (hp : 4 ≤ p) :
    Real.sqrt (6/(Real.pi*p)) + 2*Real.pi^(-p)/(p-1) < Real.sqrt (2/p) := by
  have hp0 : 0 < p := by linarith
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.2 hp0
  have hpi : (25/8 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  have hroot : Real.sqrt (6/Real.pi) < (139/100 : ℝ) := by
    have hd : 6/Real.pi < (139/100 : ℝ)^2 := by
      apply (div_lt_iff₀ Real.pi_pos).2
      nlinarith
    have hsq := Real.sq_sqrt (by positivity : 0 ≤ 6/Real.pi)
    nlinarith [Real.sqrt_nonneg (6/Real.pi)]
  have htwo : (141/100 : ℝ) < Real.sqrt 2 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hg : Real.sqrt (6/(Real.pi*p))*Real.sqrt p = Real.sqrt (6/Real.pi) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 6/(Real.pi*p))]
    congr 1
    field_simp
  have ht := scaled_ball_tail_lt_one_fiftieth p hp
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  apply (lt_div_iff₀ hsp).2
  rw [add_mul, hg]
  linarith

/-- Unconditional strict normalized sinc estimate for all real p≥4. -/
theorem ballSincIntegral_lt_sharp_of_four_le (p : ℝ) (hp : 4 ≤ p) :
    ballSincIntegral p < Real.sqrt (2/p) :=
  (ballSincIntegral_le_gaussian_add_tail p (by linarith)).trans_lt
    (ball_gaussian_tail_lt_sharp p hp)

#print axioms ballSincIntegral_le_gaussian_add_tail
#print axioms ballSincIntegral_lt_sharp_of_four_le
end CubeSections
