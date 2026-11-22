import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! The bounded Gaussian exponential score and its exact squared Lipschitz constant. -/

noncomputable section
open Set

namespace CubeSections

def gaussianScore (x : ℝ) : ℝ := Real.exp (-x ^ 2 / 6)

theorem gaussianScore_pos (x : ℝ) : 0 < gaussianScore x := Real.exp_pos _

theorem gaussianScore_le_one (x : ℝ) : gaussianScore x ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])

theorem hasDerivAt_gaussianScore (x : ℝ) :
    HasDerivAt gaussianScore ((-x / 3) * gaussianScore x) x := by
  convert ((((hasDerivAt_id x).pow 2).neg.div_const 6).exp) using 1
  · rfl
  · dsimp [gaussianScore]
    ring

theorem gaussianScore_sq (x : ℝ) : gaussianScore x ^ 2 = Real.exp (-x ^ 2 / 3) := by
  unfold gaussianScore
  rw [← Real.exp_mul_natCast]
  congr 1
  norm_num
  ring

/-- The sharp global bound for the square of the score derivative. -/
theorem gaussianScore_derivative_sq_le (x : ℝ) :
    ((-x / 3) * gaussianScore x) ^ 2 ≤ 1 / (3 * Real.exp 1) := by
  have h := Real.mul_exp_neg_le_exp_neg_one (x ^ 2 / 3)
  have hexp : Real.exp (-(x ^ 2 / 3)) = Real.exp (-x ^ 2 / 3) := by congr 1; ring
  rw [hexp, Real.exp_neg] at h
  have hid : ((-x / 3) * gaussianScore x) ^ 2 =
      ((x ^ 2 / 3) * Real.exp (-x ^ 2 / 3)) / 3 := by
    rw [mul_pow, gaussianScore_sq]
    ring
  rw [hid]
  calc
    _ ≤ (Real.exp 1)⁻¹ / 3 := div_le_div_of_nonneg_right h (by norm_num)
    _ = 1 / (3 * Real.exp 1) := by ring

theorem gaussianScore_derivative_abs_le (x : ℝ) :
    |(-x / 3) * gaussianScore x| ≤ Real.sqrt (1 / (3 * Real.exp 1)) := by
  have hc : 0 ≤ 1 / (3 * Real.exp 1) := by positivity
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  simpa only [sq_abs, Real.sq_sqrt hc] using gaussianScore_derivative_sq_le x

/-- Squared Lipschitz estimate, avoiding any convention for an NNReal square root. -/
theorem gaussianScore_difference_sq_le (x y : ℝ) :
    (gaussianScore x - gaussianScore y) ^ 2 ≤
      (1 / (3 * Real.exp 1)) * (x - y) ^ 2 := by
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (f := gaussianScore) (x := y) (y := x)
    (fun z _ => (hasDerivAt_gaussianScore z).differentiableAt)
    (fun z _ => by
      rw [(hasDerivAt_gaussianScore z).deriv, Real.norm_eq_abs]
      exact gaussianScore_derivative_abs_le z)
    convex_univ (Set.mem_univ _) (Set.mem_univ _)
  have hc : 0 ≤ 1 / (3 * Real.exp 1) := by positivity
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr hb
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hc] using hsq

theorem scaledGaussianScore_difference_sq_le (a x y : ℝ) :
    (a * gaussianScore x - a * gaussianScore y) ^ 2 ≤
      (a ^ 2 / (3 * Real.exp 1)) * (x - y) ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (gaussianScore_difference_sq_le x y) (sq_nonneg a)
  calc
    _ = a ^ 2 * (gaussianScore x - gaussianScore y) ^ 2 := by ring
    _ ≤ _ := by simpa only [div_eq_mul_inv, one_mul, mul_assoc] using h

end CubeSections
