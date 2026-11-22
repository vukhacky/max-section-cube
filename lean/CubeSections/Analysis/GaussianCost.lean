import CubeSections.Analysis.GaussianScore
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Algebraic lower bounds for the Gaussian pair cost. -/

noncomputable section

namespace CubeSections

def gaussianSecondMoment : ℝ := Real.sqrt (3 / 5 : ℝ)

def gaussianCrossMoment (s : ℝ) : ℝ := 3 / Real.sqrt (16 - s)

def gaussianPairCost (s a b : ℝ) : ℝ :=
  gaussianSecondMoment * (a ^ 2 + b ^ 2) - 2 * gaussianCrossMoment s * a * b

theorem gaussianSecondMoment_pos : 0 < gaussianSecondMoment := by
  unfold gaussianSecondMoment
  positivity

theorem gaussianSecondMoment_sq : gaussianSecondMoment ^ 2 = (3 / 5 : ℝ) := by
  exact Real.sq_sqrt (by norm_num)

theorem gaussianCrossMoment_sq (s : ℝ) (hs : s < 16) :
    gaussianCrossMoment s ^ 2 = 9 / (16 - s) := by
  unfold gaussianCrossMoment
  rw [div_pow, Real.sq_sqrt (by linarith : 0 ≤ 16 - s)]
  norm_num

theorem gaussian_moment_residual (s : ℝ) (hs : s < 16) :
    gaussianSecondMoment - gaussianCrossMoment s ^ 2 / gaussianSecondMoment =
      gaussianSecondMoment * ((1 - s) / (16 - s)) := by
  have hM : gaussianSecondMoment ≠ 0 := ne_of_gt gaussianSecondMoment_pos
  have hD := (eq_div_iff (by linarith : 16 - s ≠ 0)).mp (gaussianCrossMoment_sq s hs)
  have hMsq := gaussianSecondMoment_sq
  field_simp
  nlinarith

/-- Exact square completion, valid for arbitrary real amplitudes. -/
theorem gaussianPairCost_complete_square (s a b : ℝ) (hs : s < 16) :
    gaussianPairCost s a b =
      gaussianSecondMoment * (b - a * gaussianCrossMoment s / gaussianSecondMoment) ^ 2 +
      gaussianSecondMoment * a ^ 2 * ((1 - s) / (16 - s)) := by
  have hM : gaussianSecondMoment ≠ 0 := ne_of_gt gaussianSecondMoment_pos
  calc
    _ = gaussianSecondMoment * (b - a * gaussianCrossMoment s / gaussianSecondMoment) ^ 2 +
        a ^ 2 * (gaussianSecondMoment - gaussianCrossMoment s ^ 2 / gaussianSecondMoment) := by
      unfold gaussianPairCost
      field_simp
      ring
    _ = _ := by rw [gaussian_moment_residual s hs]; ring

/-- Normalizing at least one amplitude to one produces the sharp pair lower bound. -/
theorem gaussianPairCost_lower (s a b : ℝ) (hs : s ≤ 1) (hab : a = 1 ∨ b = 1) :
    gaussianSecondMoment * ((1 - s) / (16 - s)) ≤ gaussianPairCost s a b := by
  have hs' : s < 16 := by linarith
  rcases hab with rfl | rfl
  · rw [gaussianPairCost_complete_square s 1 b hs']
    have h := mul_nonneg gaussianSecondMoment_pos.le
      (sq_nonneg (b - 1 * gaussianCrossMoment s / gaussianSecondMoment))
    nlinarith
  · have hsym : gaussianPairCost s a 1 = gaussianPairCost s 1 a := by
      unfold gaussianPairCost
      ring
    rw [hsym, gaussianPairCost_complete_square s 1 a hs']
    have h := mul_nonneg gaussianSecondMoment_pos.le
      (sq_nonneg (a - 1 * gaussianCrossMoment s / gaussianSecondMoment))
    nlinarith

theorem gaussianPairCost_coarse_lower (s a b : ℝ) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hab : a = 1 ∨ b = 1) :
    (gaussianSecondMoment / 16) * (1 - s) ≤ gaussianPairCost s a b := by
  have hs : 0 < 16 - s := by linarith
  have hdiv : (1 - s) / 16 ≤ (1 - s) / (16 - s) :=
    div_le_div_of_nonneg_left (sub_nonneg.mpr hs₁) hs (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hdiv gaussianSecondMoment_pos.le
  have h := gaussianPairCost_lower s a b hs₁ hab
  nlinarith

theorem gaussianSecondMoment_gt_77 : (77 / 100 : ℝ) < gaussianSecondMoment := by
  have h := gaussianSecondMoment_sq
  have hp := gaussianSecondMoment_pos
  nlinarith

/-- Exact rational verification of the manuscript's global constant 20. -/
theorem global_gaussian_constant_le_twenty :
    (32 / gaussianSecondMoment) * (2 / 9 + 2 / (3 * Real.exp 1)) ≤ (20 : ℝ) := by
  have he : (8 / 3 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hden : 0 < 3 * Real.exp 1 := by positivity
  have hdiv : 2 / (3 * Real.exp 1) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hM := gaussianSecondMoment_gt_77
  have hid : (32 / gaussianSecondMoment) * (2 / 9 + 2 / (3 * Real.exp 1)) =
      (32 * (2 / 9 + 2 / (3 * Real.exp 1))) / gaussianSecondMoment := by ring
  rw [hid]
  apply (div_le_iff₀ gaussianSecondMoment_pos).mpr
  linarith

end CubeSections
