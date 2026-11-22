import CubeSections.Classical.BallThree
import CubeSections.Classical.FiniteHolder

/-! The exact second and fourth moments imply the sharp strict Ball bound
on [3,4]. Finite Hölder also gives the interpolation estimate on [2,4]. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace CubeSections

theorem ballSincIntegral_le_two_four_interpolation (p : ℝ)
    (hp : 2 ≤ p) (hp4 : p ≤ 4) :
    ballSincIntegral p ≤ (2/3 : ℝ)^((p-2)/2) := by
  let f : Fin 2 → ℝ → ℝ := ![ballSincIntegrand 2, ballSincIntegrand 4]
  let w : Fin 2 → ℝ := ![(4-p)/2, (p-2)/2]
  have hmeas : ∀ i, Measurable (f i) := by
    intro i
    fin_cases i
    · exact (continuous_ballSincIntegrand 2 (by norm_num)).measurable
    · exact (continuous_ballSincIntegrand 4 (by norm_num)).measurable
  have hpos : ∀ i x, 0 ≤ f i x := by
    intro i x
    fin_cases i <;> exact ballSincIntegrand_nonneg _ _
  have hint : ∀ i, Integrable (f i) := by
    intro i
    fin_cases i
    · exact integrable_ballSincIntegrand 2 (by norm_num)
    · exact integrable_ballSincIntegrand 4 (by norm_num)
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
      ← Real.rpow_add_of_nonneg (abs_nonneg _) (by linarith : 0 ≤ 2*((4-p)/2))
        (by linarith : 0 ≤ 4*((p-2)/2))]
    congr 1
    ring
  have hholder := (finiteHolder_nonnegative volume f w hmeas hpos hint hw hsum).2
  rw [hproduct] at hholder
  simp only [Fin.prod_univ_two, f, w, Matrix.cons_val_zero, Matrix.cons_val_one] at hholder
  change ballSincIntegral p ≤
    (ballSincIntegral 2)^((4-p)/2) * (ballSincIntegral 4)^((p-2)/2) at hholder
  simpa only [ballSincIntegral_two, ballSincIntegral_four, Real.one_rpow, one_mul] using hholder

theorem twoThirds_interpolation_lt_sqrt (p : ℝ) (hp : 3 < p) :
    (2/3 : ℝ)^((p-2)/2) < Real.sqrt (2/p) := by
  have hp0 : 0 < p := by linarith
  have hbase : Real.log (2/3 : ℝ) < -(1/3 : ℝ) := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2/3)
      (by norm_num : (2/3 : ℝ) ≠ 1)
    linarith
  have hratio : Real.log (p/3) ≤ (p-3)/3 := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < p/3)
    linarith
  have hmul := mul_lt_mul_of_pos_left hbase (by linarith : 0 < p-3)
  have hsum : (p-3)*Real.log (2/3 : ℝ) + Real.log (p/3) < 0 := by
    nlinarith
  have hlog : (p-2)*Real.log (2/3 : ℝ) < Real.log (2/p) := by
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0),
      Real.log_div (ne_of_gt hp0) (by norm_num : (3 : ℝ) ≠ 0)] at hsum
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0),
      Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hp0)]
    nlinarith
  apply (Real.log_lt_log_iff
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2/3) _)
    (Real.sqrt_pos.2 (by positivity : 0 < 2/p))).1
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2/3),
    Real.log_sqrt (by positivity : (0 : ℝ) ≤ 2/p)]
  nlinarith

theorem ballSincIntegral_lt_of_three_le_le_four (p : ℝ)
    (hp : 3 ≤ p) (hp4 : p ≤ 4) : ballSincIntegral p < Real.sqrt (2/p) := by
  rcases hp.eq_or_lt with rfl | hp
  · exact ballSincIntegral_three_lt
  · exact (ballSincIntegral_le_two_four_interpolation p (by linarith) hp4).trans_lt
      (twoThirds_interpolation_lt_sqrt p hp)

#print axioms ballSincIntegral_le_two_four_interpolation
#print axioms twoThirds_interpolation_lt_sqrt
#print axioms ballSincIntegral_lt_of_three_le_le_four
end CubeSections
