import CubeSections.Classical.BallFour
import CubeSections.Classical.BallTwo

/-! Strict Ball inequality at p=3, obtained from the exact second and fourth
moments and the positive integral of an explicit nonzero square. No strict
Cauchy--Schwarz equality theorem or global Ball bound is assumed. -/
noncomputable section
open MeasureTheory

namespace CubeSections

theorem ballSincIntegrand_nat (m : ℕ) (t : ℝ) :
    ballSincIntegrand (m : ℝ) t = |Real.sinc (Real.pi*t)|^m := by
  exact Real.rpow_natCast _ _

theorem integrable_absSinc_pow (m : ℕ) (hm : 2 ≤ m) :
    Integrable (fun t : ℝ => |Real.sinc (Real.pi*t)|^m) := by
  have h : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have heq : ballSincIntegrand (m : ℝ) = fun t : ℝ => |Real.sinc (Real.pi*t)|^m :=
    funext (ballSincIntegrand_nat m)
  rw [← heq]
  exact integrable_ballSincIntegrand _ h

theorem integral_absSinc_pow (m : ℕ) :
    (∫ t : ℝ, |Real.sinc (Real.pi*t)|^m) = ballSincIntegral (m : ℝ) := by
  simp only [ballSincIntegral]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => (ballSincIntegrand_nat m t).symm)

theorem ballSincIntegral_three_lt : ballSincIntegral 3 < Real.sqrt (2/3) := by
  let a : ℝ := Real.sqrt (2/3)
  let f : ℝ → ℝ := fun t => |Real.sinc (Real.pi*t)|
  have ha : 0 < a := Real.sqrt_pos.2 (by norm_num)
  have ha2 : a^2 = (2/3 : ℝ) := Real.sq_sqrt (by norm_num)
  have ha1 : a ≠ 1 := by nlinarith
  have h2 : Integrable (fun t : ℝ => f t^2) := integrable_absSinc_pow 2 (by norm_num)
  have h3 : Integrable (fun t : ℝ => f t^3) := integrable_absSinc_pow 3 (by norm_num)
  have h4 : Integrable (fun t : ℝ => f t^4) := integrable_absSinc_pow 4 (by norm_num)
  have heq : (fun t : ℝ => (a*f t-f t^2)^2) =
      fun t : ℝ => a^2*f t^2 - (2*a)*f t^3 + f t^4 := by
    funext t
    ring
  have hi : Integrable (fun t : ℝ => (a*f t-f t^2)^2) := by
    rw [heq]
    exact ((h2.const_mul _).sub (h3.const_mul _)).add h4
  have hc : Continuous (fun t : ℝ => (a*f t-f t^2)^2) := by
    dsimp [f]
    fun_prop
  have hz : (a*f 0-f 0^2)^2 ≠ 0 := by
    simpa only [f, mul_zero, Real.sinc_zero, abs_one, mul_one, one_pow,
      ne_eq, sq_eq_zero_iff, sub_eq_zero] using ha1
  have hp : 0 < ∫ t : ℝ, (a*f t-f t^2)^2 :=
    integral_pos_of_integrable_nonneg_ne_zero hc hi (fun t => sq_nonneg _) hz
  have hadd := integral_add ((h2.const_mul (a^2)).sub (h3.const_mul (2*a))) h4
  simp only [Pi.sub_apply] at hadd
  rw [heq, hadd,
    integral_sub (h2.const_mul (a^2)) (h3.const_mul (2*a)), integral_const_mul,
    integral_const_mul] at hp
  change 0 < a^2*(∫ t : ℝ, |Real.sinc (Real.pi*t)|^2) -
    (2*a)*(∫ t : ℝ, |Real.sinc (Real.pi*t)|^3) +
    (∫ t : ℝ, |Real.sinc (Real.pi*t)|^4) at hp
  rw [integral_absSinc_pow, integral_absSinc_pow, integral_absSinc_pow] at hp
  norm_num only [Nat.cast_ofNat] at hp
  rw [ballSincIntegral_two, ballSincIntegral_four, ha2] at hp
  change ballSincIntegral 3 < a
  nlinarith

#print axioms ballSincIntegral_three_lt
end CubeSections
