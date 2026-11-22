import CubeSections.Classical.TentDensity
import CubeSections.Classical.SincIntegrability
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Exact fourth sinc moment. The triangular density is the actual convolution
of two uniform unit intervals. Fourier inversion and Fourier pairing identify
its squared integral with the fourth sinc moment. No Ball inequality is used. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace CubeSections

theorem fourier_nonnegative_real_density_eq_charFun (f : ℝ → ℝ)
    (hmeas : Measurable f) (hpos : ∀ x, 0 ≤ f x) (t : ℝ) :
    𝓕 (fun x => (f x : ℂ)) t =
      charFun (volume.withDensity (fun x => ENNReal.ofReal (f x))) ((-2*Real.pi) • t) := by
  rw [Real.fourier_eq', charFun_apply,
    integral_withDensity_eq_integral_toReal_smul hmeas.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (hpos x), inner_smul_right, Complex.real_smul]
    simp only [smul_eq_mul]
    rw [mul_comm (f x : ℂ)])

theorem fourier_tentDensity (t : ℝ) :
    𝓕 (fun x => (tentDensity x : ℂ)) t = (Real.sinc (Real.pi*t) : ℂ)^2 := by
  rw [fourier_nonnegative_real_density_eq_charFun tentDensity
    measurable_tentDensity tentDensity_nonneg, ← map_add_unitIntervalMeasure]
  change charFun (unitIntervalMeasure ∗ unitIntervalMeasure) ((-2*Real.pi)*t) = _
  rw [charFun_conv, charFun_unitIntervalMeasure_neg_two_pi]
  ring

theorem integrable_sincSquared : Integrable (fun t : ℝ => Real.sinc (Real.pi*t)^2) := by
  have hfun : ballSincIntegrand 2 = fun t : ℝ => Real.sinc (Real.pi*t)^2 := by
    funext t
    simp only [ballSincIntegrand, Real.rpow_two, sq_abs]
  rw [← hfun]
  exact integrable_ballSincIntegrand 2 (by norm_num)

theorem integrable_complex_sincSquared :
    Integrable (fun t : ℝ => (Real.sinc (Real.pi*t) : ℂ)^2) := by
  simpa only [Complex.ofReal_pow] using
    (integrable_sincSquared.ofReal :
      Integrable (fun t : ℝ => ((Real.sinc (Real.pi*t)^2 : ℝ) : ℂ)))

theorem fourier_sincSquared (t : ℝ) :
    𝓕 (fun x : ℝ => (Real.sinc (Real.pi*x) : ℂ)^2) t = (tentDensity t : ℂ) := by
  have hF : 𝓕 (fun x => (tentDensity x : ℂ)) =
      fun x => (Real.sinc (Real.pi*x) : ℂ)^2 := funext fourier_tentDensity
  have hFi : Integrable (𝓕 (fun x => (tentDensity x : ℂ))) := by
    rw [hF]
    exact integrable_complex_sincSquared
  have hc : ContinuousAt (fun x => (tentDensity x : ℂ)) (-t) :=
    Complex.continuous_ofReal.continuousAt.comp continuous_tentDensity.continuousAt
  have hinv := integrable_tentDensity.ofReal.fourierInv_fourier_eq hFi hc
  rw [hF, Real.fourierInv_eq_fourier_neg, neg_neg, tentDensity_neg] at hinv
  exact hinv

theorem integral_sinc_four :
    (∫ t : ℝ, Real.sinc (Real.pi*t)^4) = (2/3 : ℝ) := by
  have hpair :
      (∫ t : ℝ, (𝓕 (fun x => (tentDensity x : ℂ)) t) *
        (Real.sinc (Real.pi*t) : ℂ)^2) =
      ∫ x : ℝ, (tentDensity x : ℂ) *
        𝓕 (fun t : ℝ => (Real.sinc (Real.pi*t) : ℂ)^2) x := by
    simpa only [flip_innerₗ, smul_eq_mul] using!
      (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
        Real.continuous_fourierChar continuous_inner
        integrable_tentDensity.ofReal integrable_complex_sincSquared)
  simp_rw [fourier_tentDensity, fourier_sincSquared] at hpair
  have hleft :
      (fun t : ℝ => (Real.sinc (Real.pi*t) : ℂ)^2 * (Real.sinc (Real.pi*t) : ℂ)^2) =
      fun t : ℝ => ((Real.sinc (Real.pi*t)^4 : ℝ) : ℂ) := by
    funext t
    push_cast
    ring
  have hright : (fun t : ℝ => (tentDensity t : ℂ) * (tentDensity t : ℂ)) =
      fun t : ℝ => ((tentDensity t^2 : ℝ) : ℂ) := by
    funext t
    push_cast
    ring
  rw [hleft, hright, integral_complex_ofReal, integral_complex_ofReal] at hpair
  exact (Complex.ofReal_injective hpair).trans integral_tentDensity_sq

theorem ballSincIntegral_four : ballSincIntegral 4 = (2/3 : ℝ) := by
  have hfun : ballSincIntegrand 4 = fun t : ℝ => Real.sinc (Real.pi*t)^4 := by
    funext t
    rw [ballSincIntegrand, show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
    simp only [show (4 : ℕ) = 2*2 by norm_num, pow_mul, sq_abs]
  rw [ballSincIntegral, hfun, integral_sinc_four]

theorem ballSincIntegral_four_lt : ballSincIntegral 4 < Real.sqrt (2/4) := by
  rw [ballSincIntegral_four]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2/4)
  have hp := Real.sqrt_nonneg (2/4)
  nlinarith

#print axioms fourier_tentDensity
#print axioms fourier_sincSquared
#print axioms integral_sinc_four
#print axioms ballSincIntegral_four
#print axioms ballSincIntegral_four_lt
end CubeSections
