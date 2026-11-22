import CubeSections.Certificates.Coverage
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Real-variable consequences of the exact rational angular test. -/
namespace CubeSections.Certificates

/-- The squared sufficient inequality has the intended positive square-root interpretation. -/
theorem angular_test_sound_real {S K v : ℝ}
    (hS : 0 ≤ S) (hK : 0 < K) (hv : 0 ≤ v)
    (htest : 5 * (S * K * (15 + v)) ^ 2 < 3 * v ^ 2) :
    S < Real.sqrt (3 / 5) * v / ((15 + v) * K) := by
  have hden : 0 < (15 + v) * K := mul_pos (by linarith) hK
  have hleft : 0 ≤ S * K * (15 + v) := by positivity
  have hright : 0 ≤ Real.sqrt (3 / 5) * v := by positivity
  have hsqrt : (Real.sqrt (3 / 5)) ^ 2 = (3 : ℝ) / 5 :=
    Real.sq_sqrt (by norm_num)
  have hsq : (S * K * (15 + v)) ^ 2 < (Real.sqrt (3 / 5) * v) ^ 2 := by
    simp only [mul_pow, hsqrt]
    nlinarith
  have hlin := (sq_lt_sq₀ hleft hright).mp hsq
  apply (lt_div_iff₀ hden).mpr
  nlinarith

/-- Exact Rat acceptance casts to a genuine real angular lower bound. -/
theorem AngleTest.sound {S K v : ℚ}
    (hS : 0 ≤ S) (hK : 0 < K) (hv : 0 ≤ v) (h : AngleTest S K v) :
    (S : ℝ) < Real.sqrt (3 / 5) * (v : ℝ) / ((15 + (v : ℝ)) * (K : ℝ)) := by
  apply angular_test_sound_real
  · exact_mod_cast hS
  · exact_mod_cast hK
  · exact_mod_cast hv
  · unfold AngleTest at h
    exact_mod_cast h

/-- The angular lower bound increases with the squared sine of the angle. -/
theorem angular_fraction_monotone {K v w : ℝ}
    (hK : 0 < K) (hv : 0 ≤ v) (hvw : v ≤ w) :
    Real.sqrt (3 / 5) * v / ((15 + v) * K) ≤
      Real.sqrt (3 / 5) * w / ((15 + w) * K) := by
  have hw : 0 ≤ w := hv.trans hvw
  have hdv : 0 < (15 + v) * K := mul_pos (by linarith) hK
  have hdw : 0 < (15 + w) * K := mul_pos (by linarith) hK
  apply (div_le_div_iff₀ hdv hdw).mpr
  have hs : 0 ≤ Real.sqrt ((3 : ℝ) / 5) := Real.sqrt_nonneg _
  have hprod : 0 ≤ Real.sqrt ((3 : ℝ) / 5) * K * (w - v) := by positivity
  nlinarith

/-- Once a rectangle's angular test succeeds, it holds for every larger squared sine. -/
theorem AngleTest.sound_of_le {S K v : ℚ} {w : ℝ}
    (hS : 0 ≤ S) (hK : 0 < K) (hv : 0 ≤ v) (h : AngleTest S K v)
    (hvw : (v : ℝ) ≤ w) :
    (S : ℝ) < Real.sqrt (3 / 5) * w / ((15 + w) * (K : ℝ)) := by
  exact (h.sound hS hK hv).trans_le
    (angular_fraction_monotone (by exact_mod_cast hK) (by exact_mod_cast hv) hvw)

/-- A larger denominator gives a smaller nonnegative angular bound. -/
theorem angular_denominator_antitone {K D v : ℝ}
    (hD : 0 < D) (hDK : D ≤ K) (hv : 0 ≤ v) :
    Real.sqrt (3 / 5) * v / ((15 + v) * K) ≤
      Real.sqrt (3 / 5) * v / ((15 + v) * D) := by
  apply div_le_div_of_nonneg_left (by positivity)
  · exact mul_pos (by linarith) hD
  · exact mul_le_mul_of_nonneg_left hDK (by linarith)

/-- Projection lower bound, expressed directly with positive class weights. -/
theorem complementary_projection_bound {a b A B s : ℝ}
    (ha : 0 < a) (hb : 0 < b) (haA : a ≤ A) (hbB : b ≤ B)
    (hA : A ≤ 1) (hB : B ≤ 1)
    (hs : s ≤ (1 - A) * (1 - B) / (A * B)) :
    1 - (1 - a) * (1 - b) / (a * b) ≤ 1 - s := by
  have hAp : 0 < A := ha.trans_le haA
  have hBp : 0 < B := hb.trans_le hbB
  have hfirst : (1 - A) / A ≤ (1 - a) / a := by
    apply (div_le_div_iff₀ hAp ha).mpr
    nlinarith
  have hsecond : (1 - B) / B ≤ (1 - b) / b := by
    apply (div_le_div_iff₀ hBp hb).mpr
    nlinarith
  have hprod : ((1 - A) / A) * ((1 - B) / B) ≤
      ((1 - a) / a) * ((1 - b) / b) := by
    apply mul_le_mul hfirst hsecond
    · exact div_nonneg (by linarith) hBp.le
    · exact div_nonneg (by linarith) ha.le
  rw [← mul_div_mul_comm, ← mul_div_mul_comm] at hprod
  linarith

#print axioms angular_test_sound_real
#print axioms AngleTest.sound
#print axioms angular_fraction_monotone
#print axioms complementary_projection_bound

end CubeSections.Certificates
