import CubeSections.Analysis.SincCubicIntegrals
import CubeSections.Classical.CubicLobeAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! A rationally controlled integral on the first negative sinc lobe. -/

noncomputable section
open Set MeasureTheory

namespace CubeSections

private def cubicLobeLeft (s : ℝ) : ℝ := Real.sin (Real.pi * s) ^ 3 / (1 + s) ^ 3
private def cubicLobeRight (s : ℝ) : ℝ := Real.sin (Real.pi * s) ^ 3 / (2 - s) ^ 3

private theorem cubicLobeLeft_integrable : IntervalIntegrable cubicLobeLeft volume (0 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  apply ContinuousOn.div
    (by fun_prop : ContinuousOn (fun s : ℝ => Real.sin (Real.pi * s) ^ 3) (Icc 0 1))
    (by fun_prop : ContinuousOn (fun s : ℝ => (1 + s) ^ 3) (Icc 0 1))
  intro s hs
  exact pow_ne_zero 3 (by linarith [hs.1])

private theorem cubicLobeRight_integrable : IntervalIntegrable cubicLobeRight volume (0 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  apply ContinuousOn.div
    (by fun_prop : ContinuousOn (fun s : ℝ => Real.sin (Real.pi * s) ^ 3) (Icc 0 1))
    (by fun_prop : ContinuousOn (fun s : ℝ => (2 - s) ^ 3) (Icc 0 1))
  intro s hs
  exact pow_ne_zero 3 (by linarith [hs.2])

private theorem cubicLobe_reflection :
    (∫ s in (0 : ℝ)..1, cubicLobeRight s) = ∫ s in (0 : ℝ)..1, cubicLobeLeft s := by
  have hfun : (fun s : ℝ => cubicLobeLeft (1 - s)) = cubicLobeRight := by
    funext s
    unfold cubicLobeLeft cubicLobeRight
    rw [show Real.pi * (1 - s) = Real.pi - Real.pi * s by ring, Real.sin_pi_sub]
    congr 2
    ring
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) cubicLobeLeft 1
  simpa only [hfun, sub_self, sub_zero] using h

private theorem cubicLobeLeft_bound :
    (∫ s in (0 : ℝ)..1, cubicLobeLeft s) ≤ 3 / (4 * Real.pi) - 80 / (27 * Real.pi ^ 3) := by
  have hi : IntervalIntegrable (fun s => cubicLobeLeft s + cubicLobeRight s) volume (0 : ℝ) 1 :=
    cubicLobeLeft_integrable.add cubicLobeRight_integrable
  have hj : IntervalIntegrable (fun s => Real.sin (Real.pi * s) ^ 3 * ((9 / 8 : ℝ) - 2 * s * (1 - s)))
      volume (0 : ℝ) 1 := (by fun_prop : Continuous
        (fun s : ℝ => Real.sin (Real.pi * s) ^ 3 * ((9 / 8 : ℝ) - 2 * s * (1 - s)))).intervalIntegrable 0 1
  have hb := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hi hj (fun s hs => by
    have hsin : 0 ≤ Real.sin (Real.pi * s) := Real.sin_nonneg_of_mem_Icc
      ⟨mul_nonneg Real.pi_pos.le hs.1, mul_le_of_le_one_right Real.pi_pos.le hs.2⟩
    calc
      cubicLobeLeft s + cubicLobeRight s = Real.sin (Real.pi * s) ^ 3 *
          (1 / (1 + s) ^ 3 + 1 / (2 - s) ^ 3) := by unfold cubicLobeLeft cubicLobeRight; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (cubic_first_lobe_weight_bound s hs.1 hs.2)
        (pow_nonneg hsin 3))
  rw [intervalIntegral.integral_add cubicLobeLeft_integrable cubicLobeRight_integrable,
    cubicLobe_reflection, integral_cubic_weight_majorant] at hb
  have heq : 3 / (2 * Real.pi) - 160 / (27 * Real.pi ^ 3) =
      2 * (3 / (4 * Real.pi) - 80 / (27 * Real.pi ^ 3)) := by field_simp; ring
  rw [heq] at hb
  linarith

private theorem abs_sinc_pi_one_add {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    |Real.sinc (Real.pi * (1 + s))| = Real.sin (Real.pi * s) / (Real.pi * (1 + s)) := by
  have hd : 0 < Real.pi * (1 + s) := mul_pos Real.pi_pos (by linarith [hs.1])
  have hsin : 0 ≤ Real.sin (Real.pi * s) := Real.sin_nonneg_of_mem_Icc
    ⟨mul_nonneg Real.pi_pos.le hs.1, mul_le_of_le_one_right Real.pi_pos.le hs.2⟩
  rw [Real.sinc_of_ne_zero (ne_of_gt hd), abs_div, abs_of_pos hd,
    show Real.sin (Real.pi * (1 + s)) = -Real.sin (Real.pi * s) by
      rw [show Real.pi * (1 + s) = Real.pi * s + Real.pi by ring, Real.sin_add_pi],
    abs_neg, abs_of_nonneg hsin]

theorem integral_first_sinc_lobe_cubed :
    (∫ t in (1 : ℝ)..2, |Real.sinc (Real.pi * t)| ^ 3) ≤
      3 / (4 * Real.pi ^ 4) - 80 / (27 * Real.pi ^ 6) := by
  have hshift : (∫ t in (1 : ℝ)..2, |Real.sinc (Real.pi * t)| ^ 3) =
      ∫ s in (0 : ℝ)..1, |Real.sinc (Real.pi * (1 + s))| ^ 3 := by
    convert (intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := 1)
      (fun t : ℝ => |Real.sinc (Real.pi * t)| ^ 3) 1).symm using 1 <;> norm_num
  have hid : (∫ s in (0 : ℝ)..1, |Real.sinc (Real.pi * (1 + s))| ^ 3) =
      (1 / Real.pi ^ 3) * (∫ s in (0 : ℝ)..1, cubicLobeLeft s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    change |Real.sinc (Real.pi * (1 + s))| ^ 3 = (1 / Real.pi ^ 3) * cubicLobeLeft s
    rw [abs_sinc_pi_one_add hs]
    have hsne : 1 + s ≠ 0 := by linarith [hs.1]
    unfold cubicLobeLeft
    field_simp [Real.pi_ne_zero, hsne] <;> ring
  rw [hshift, hid]
  calc
    _ ≤ (1 / Real.pi ^ 3) * (3 / (4 * Real.pi) - 80 / (27 * Real.pi ^ 3)) :=
      mul_le_mul_of_nonneg_left cubicLobeLeft_bound (by positivity)
    _ = _ := by field_simp

end CubeSections
