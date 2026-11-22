import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Rational algebra for a certified absolute cubic sinc bound. -/
noncomputable section
namespace CubeSections

theorem cubic_first_lobe_weight_bound (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    1/(1+s)^3 + 1/(2-s)^3 ≤ (9:ℝ)/8 - 2*s*(1-s) := by
  let z : ℝ := s*(1-s)
  have hz0 : 0 ≤ z := mul_nonneg hs0 (sub_nonneg.mpr hs1)
  have hz1 : z ≤ 1/4 := by dsimp [z]; nlinarith [sq_nonneg (s-1/2)]
  have hz2 : z^2 ≤ (1/4:ℝ)^2 := pow_le_pow_left₀ hz0 hz1 2
  have hz3 : z^3 ≤ (1/4:ℝ)^3 := pow_le_pow_left₀ hz0 hz1 3
  have hq : 0 ≤ 52 - 138*z - 87*z^2 - 16*z^3 := by nlinarith
  have h1 : 0 < 1+s := by linarith
  have h2 : 0 < 2-s := by linarith
  rw [div_add_div 1 1 (ne_of_gt (pow_pos h1 3)) (ne_of_gt (pow_pos h2 3))]
  apply (div_le_iff₀ (mul_pos (pow_pos h1 3) (pow_pos h2 3))).mpr
  have heq : ((9:ℝ)/8 - 2*s*(1-s))*((1+s)^3*(2-s)^3) -
      (1*(2-s)^3+1*(1+s)^3) = z*(52-138*z-87*z^2-16*z^3)/8 := by
    dsimp [z]
    ring
  have hn : 0 ≤ z*(52-138*z-87*z^2-16*z^3)/8 := by positivity
  linarith

theorem cubic_negative_lobe_constant_lt :
    (3:ℝ)/(4*Real.pi^4) - 80/(27*Real.pi^6) + 1/(18*Real.pi^3) < 1/144 := by
  have hpiL : (25:ℝ)/8 ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hpiU : Real.pi ≤ (22:ℝ)/7 := by linarith [Real.pi_lt_d4]
  have hx0 : 0 ≤ Real.pi⁻¹ := inv_nonneg.mpr Real.pi_pos.le
  have hxL : (7:ℝ)/22 ≤ Real.pi⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ Real.pi_pos]
    linarith
  have hxU : Real.pi⁻¹ ≤ (8:ℝ)/25 := by
    rw [inv_eq_one_div, div_le_iff₀ Real.pi_pos]
    linarith
  have h3 := pow_le_pow_left₀ hx0 hxU 3
  have h4 := pow_le_pow_left₀ hx0 hxU 4
  have h6 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 7/22) hxL 6
  have heq : (3:ℝ)/(4*Real.pi^4) - 80/(27*Real.pi^6) + 1/(18*Real.pi^3) =
      (3/4:ℝ)*(Real.pi⁻¹)^4 - (80/27:ℝ)*(Real.pi⁻¹)^6 + (1/18:ℝ)*(Real.pi⁻¹)^3 := by
    field_simp
  rw [heq]
  calc
    _ ≤ (3/4:ℝ)*(8/25:ℝ)^4 - (80/27:ℝ)*(7/22:ℝ)^6 + (1/18:ℝ)*(8/25:ℝ)^3 := by
      nlinarith only [h3,h4,h6]
    _ < 1/144 := by norm_num

#print axioms cubic_first_lobe_weight_bound
#print axioms cubic_negative_lobe_constant_lt
end CubeSections
