import CubeSections.Classical.SincNegative
import CubeSections.Analysis.SincFirstLobe
import CubeSections.Analysis.SincGaussianEnvelope
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The actual negative cubic sinc mass on the positive half-line. The first
negative lobe uses its proved rationally weighted bound. Subsequent lobes are
bounded by the full cubic power tail beyond 3. Positive lobes contribute zero. -/
noncomputable section
open Set MeasureTheory
namespace CubeSections

theorem sinc_nonneg_on_zero_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ Real.sinc (Real.pi*t) := by
  apply sinc_nonneg_central
  exact ⟨mul_nonneg Real.pi_pos.le ht.1,
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 Real.pi_pos.le⟩

theorem sinc_nonneg_on_two_three {t : ℝ} (ht : t ∈ Icc (2 : ℝ) 3) :
    0 ≤ Real.sinc (Real.pi*t) := by
  have ht0 : 0 < t := by linarith [ht.1]
  rw [Real.sinc_of_ne_zero (ne_of_gt (mul_pos Real.pi_pos ht0))]
  apply div_nonneg _ (mul_pos Real.pi_pos ht0).le
  have heq : Real.pi*t = Real.pi*(t-2) + 2*Real.pi := by ring
  rw [heq, Real.sin_add_two_pi]
  exact Real.sin_nonneg_of_mem_Icc ⟨mul_nonneg Real.pi_pos.le (by linarith [ht.1]),
    by nlinarith [Real.pi_pos, ht.2]⟩

theorem sinc_negative_cube_le_abs_cube (t : ℝ) :
    max (-(Real.sinc (Real.pi*t))^3) 0 ≤ |Real.sinc (Real.pi*t)|^3 := by
  apply max_le
  · rw [pow_abs]
    exact neg_le_abs _
  · exact pow_nonneg (abs_nonneg _) _

theorem sinc_negative_cube_eq_zero_of_nonneg {t : ℝ}
    (ht : 0 ≤ Real.sinc (Real.pi*t)) : max (-(Real.sinc (Real.pi*t))^3) 0 = 0 :=
  max_eq_right (neg_nonpos.mpr (pow_nonneg ht _))

def sincCubicFirstMajorant (t : ℝ) : ℝ :=
  (Ioc (1 : ℝ) 2).indicator (fun x => |Real.sinc (Real.pi*x)|^3) t

def sincCubicTailMajorant (t : ℝ) : ℝ :=
  (Ioi (3 : ℝ)).indicator (fun x : ℝ => Real.pi^(-3 : ℝ)*x^(-3 : ℝ)) t

theorem sincCubicFirstMajorant_nonneg (t : ℝ) : 0 ≤ sincCubicFirstMajorant t :=
  Set.indicator_nonneg (fun _ _ => pow_nonneg (abs_nonneg _) _) t

theorem sincCubicTailMajorant_nonneg (t : ℝ) : 0 ≤ sincCubicTailMajorant t := by
  apply Set.indicator_nonneg _ t
  intro x hx
  exact mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
    (Real.rpow_nonneg (by linarith [mem_Ioi.mp hx]) _)

theorem integrable_sincCubicFirstMajorant : Integrable sincCubicFirstMajorant :=
  (integrable_absSinc_pow 3 (by norm_num)).integrableOn.integrable_indicator measurableSet_Ioc

theorem integrable_sincCubicTailMajorant : Integrable sincCubicTailMajorant := by
  have h : IntegrableOn (fun x : ℝ => Real.pi^(-3 : ℝ)*x^(-3 : ℝ)) (Ioi (3 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 3)).const_mul (Real.pi^(-3 : ℝ))
  exact h.integrable_indicator measurableSet_Ioi

theorem integral_sincCubicTailMajorant :
    (∫ t, sincCubicTailMajorant t) = 1/(18*Real.pi^3) := by
  change (∫ t : ℝ, (Ioi (3 : ℝ)).indicator
    (fun x : ℝ => Real.pi^(-3 : ℝ)*x^(-3 : ℝ)) t) = _
  rw [integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) (by norm_num : (0 : ℝ) < 3)]
  norm_num [Real.rpow_neg Real.pi_pos.le, Real.rpow_ofNat]

theorem sinc_negative_cube_le_tail {t : ℝ} (ht : 3 < t) :
    max (-(Real.sinc (Real.pi*t))^3) 0 ≤ Real.pi^(-3 : ℝ)*t^(-3 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hs : |Real.sinc (Real.pi*t)| ≤ 1/(Real.pi*t) := by
    rw [Real.sinc_of_ne_zero (ne_of_gt (mul_pos Real.pi_pos ht0)), abs_div,
      abs_of_pos (mul_pos Real.pi_pos ht0)]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (mul_pos Real.pi_pos ht0).le
  calc
    _ ≤ |Real.sinc (Real.pi*t)|^3 := sinc_negative_cube_le_abs_cube t
    _ ≤ (1/(Real.pi*t))^3 := pow_le_pow_left₀ (abs_nonneg _) hs 3
    _ = _ := by
      simp only [Real.rpow_neg Real.pi_pos.le, Real.rpow_neg ht0.le,
        Real.rpow_ofNat, div_pow, one_pow, mul_pow]
      ring

theorem sinc_negative_cube_le_majorants {t : ℝ} (ht : 0 < t) :
    max (-(Real.sinc (Real.pi*t))^3) 0 ≤
      sincCubicFirstMajorant t + sincCubicTailMajorant t := by
  by_cases ht1 : t ≤ 1
  · rw [sinc_negative_cube_eq_zero_of_nonneg (sinc_nonneg_on_zero_one ⟨ht.le, ht1⟩)]
    exact add_nonneg (sincCubicFirstMajorant_nonneg t) (sincCubicTailMajorant_nonneg t)
  · have ht1' : 1 < t := lt_of_not_ge ht1
    by_cases ht2 : t ≤ 2
    · have heq : sincCubicFirstMajorant t = |Real.sinc (Real.pi*t)|^3 := by
        unfold sincCubicFirstMajorant
        rw [Set.indicator_of_mem (show t ∈ Ioc (1 : ℝ) 2 from ⟨ht1', ht2⟩)]
      rw [heq]
      exact (sinc_negative_cube_le_abs_cube t).trans (le_add_of_nonneg_right (sincCubicTailMajorant_nonneg t))
    · by_cases ht3 : t ≤ 3
      · rw [sinc_negative_cube_eq_zero_of_nonneg
          (sinc_nonneg_on_two_three ⟨(lt_of_not_ge ht2).le, ht3⟩)]
        exact add_nonneg (sincCubicFirstMajorant_nonneg t) (sincCubicTailMajorant_nonneg t)
      · have ht3' : 3 < t := lt_of_not_ge ht3
        have heq : sincCubicTailMajorant t = Real.pi^(-3 : ℝ)*t^(-3 : ℝ) :=
          Set.indicator_of_mem ht3' _
        rw [heq]
        exact (sinc_negative_cube_le_tail ht3').trans
          (le_add_of_nonneg_left (sincCubicFirstMajorant_nonneg t))

/-- Exact analytic cap before the final rational comparison with 1/144. -/
theorem sinc_negative_cube_halfline_bound :
    (∫ t in Ioi (0 : ℝ), max (-(Real.sinc (Real.pi*t))^3) 0) ≤
      3/(4*Real.pi^4) - 80/(27*Real.pi^6) + 1/(18*Real.pi^3) := by
  have hsum := integrable_sincCubicFirstMajorant.add integrable_sincCubicTailMajorant
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), sincCubicFirstMajorant t + sincCubicTailMajorant t :=
      setIntegral_mono_on integrable_sinc_negative_cube.integrableOn hsum.integrableOn
        measurableSet_Ioi (fun t ht => sinc_negative_cube_le_majorants ht)
    _ ≤ ∫ t : ℝ, sincCubicFirstMajorant t + sincCubicTailMajorant t :=
      setIntegral_le_integral hsum (ae_of_all _ (fun t =>
        add_nonneg (sincCubicFirstMajorant_nonneg t) (sincCubicTailMajorant_nonneg t)))
    _ = (∫ t : ℝ in (1 : ℝ)..2, |Real.sinc (Real.pi*t)|^3) + 1/(18*Real.pi^3) := by
      rw [integral_add integrable_sincCubicFirstMajorant integrable_sincCubicTailMajorant,
        integral_sincCubicTailMajorant]
      congr 1
      change (∫ t : ℝ, (Ioc (1 : ℝ) 2).indicator (fun x => |Real.sinc (Real.pi*x)|^3) t) = _
      rw [integral_indicator measurableSet_Ioc,
        intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    _ ≤ _ := by linarith [integral_first_sinc_lobe_cubed]

#print axioms sinc_negative_cube_halfline_bound
end CubeSections
