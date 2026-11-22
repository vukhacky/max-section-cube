import CubeSections.Classical.BallInterpolation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Near-two reduction of the strict Ball bound to the single quantitative
third-moment estimate I3≤7/9. All logarithm constants and Holder interpolation
are proved here; the third-moment estimate is an explicit hypothesis. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubeSections

theorem ballSincIntegral_le_two_three_interpolation (p : ℝ)
    (hp : 2 ≤ p) (hp3 : p ≤ 3) :
    ballSincIntegral p ≤ (ballSincIntegral 3)^(p-2) := by
  let f : Fin 2 → ℝ → ℝ := ![ballSincIntegrand 2, ballSincIntegrand 3]
  let w : Fin 2 → ℝ := ![3-p, p-2]
  have hmeas : ∀ i, Measurable (f i) := by
    intro i
    fin_cases i
    · exact (continuous_ballSincIntegrand 2 (by norm_num)).measurable
    · exact (continuous_ballSincIntegrand 3 (by norm_num)).measurable
  have hpos : ∀ i x, 0 ≤ f i x := by
    intro i x
    fin_cases i <;> exact ballSincIntegrand_nonneg _ _
  have hint : ∀ i, Integrable (f i) := by
    intro i
    fin_cases i
    · exact integrable_ballSincIntegrand 2 (by norm_num)
    · exact integrable_ballSincIntegrand 3 (by norm_num)
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    fin_cases i <;> dsimp [w] <;> linarith
  have hsum : ∑ i, w i = 1 := by
    simp only [Fin.sum_univ_two, w, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hproduct : (fun t : ℝ => ∏ i, (f i t)^w i) = ballSincIntegrand p := by
    funext t
    simp only [Fin.prod_univ_two, f, w, Matrix.cons_val_zero, Matrix.cons_val_one,
      ballSincIntegrand]
    rw [← Real.rpow_mul (abs_nonneg _), ← Real.rpow_mul (abs_nonneg _),
      ← Real.rpow_add_of_nonneg (abs_nonneg _) (by linarith : 0 ≤ 2*(3-p))
        (by linarith : 0 ≤ 3*(p-2))]
    congr 1
    ring
  have hholder := (finiteHolder_nonnegative volume f w hmeas hpos hint hw hsum).2
  rw [hproduct] at hholder
  simp only [Fin.prod_univ_two, f, w, Matrix.cons_val_zero, Matrix.cons_val_one] at hholder
  change ballSincIntegral p ≤ (ballSincIntegral 2)^(3-p) * (ballSincIntegral 3)^(p-2) at hholder
  simpa only [ballSincIntegral_two, Real.one_rpow, one_mul] using hholder

theorem log_sevenNinths_lt : Real.log (7/9 : ℝ) < -(1/4 : ℝ) := by
  have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1/8)
    (by norm_num : (1/8 : ℝ) < 1) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (7/9 : ℝ) = -Real.log (9/7 : ℝ) := by
    rw [show (7/9 : ℝ) = (9/7 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [heq]
  linarith

theorem sevenNinths_interpolation_lt_sqrt (p : ℝ) (hp : 2 < p) :
    (7/9 : ℝ)^(p-2) < Real.sqrt (2/p) := by
  have hp0 : 0 < p := by linarith
  have hratio := Real.log_le_sub_one_of_pos (by positivity : 0 < p/2)
  have hmul := mul_lt_mul_of_pos_left log_sevenNinths_lt (by linarith : 0 < p-2)
  have hlog : (p-2)*Real.log (7/9 : ℝ) < Real.log (2/p)/2 := by
    rw [Real.log_div (ne_of_gt hp0) (by norm_num : (2 : ℝ) ≠ 0)] at hratio
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hp0)]
    nlinarith
  apply (Real.log_lt_log_iff
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 7/9) _)
    (Real.sqrt_pos.2 (by positivity : 0 < 2/p))).1
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 7/9),
    Real.log_sqrt (by positivity : (0 : ℝ) ≤ 2/p)]
  exact hlog

theorem ballSincIntegral_lt_of_two_lt_le_three
    (hI3 : ballSincIntegral 3 ≤ (7/9 : ℝ)) (p : ℝ)
    (hp : 2 < p) (hp3 : p ≤ 3) : ballSincIntegral p < Real.sqrt (2/p) := by
  apply (ballSincIntegral_le_two_three_interpolation p hp.le hp3).trans_lt
  have hpow : (ballSincIntegral 3)^(p-2) ≤ (7/9 : ℝ)^(p-2) :=
    Real.rpow_le_rpow (ballSincIntegral_pos_of_two_le 3 (by norm_num)).le hI3 (by linarith)
  exact hpow.trans_lt (sevenNinths_interpolation_lt_sqrt p hp)

#print axioms ballSincIntegral_le_two_three_interpolation
#print axioms log_sevenNinths_lt
#print axioms ballSincIntegral_lt_of_two_lt_le_three
end CubeSections
