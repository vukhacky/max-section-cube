import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! One-dimensional normalization and finite-product consequences of Ball's
scalar bound. `StrictBallSincBound` specifies the analytic hypothesis used in
these implications; `Classical.BallProved` proves it. All integrals use the
manuscript's π normalization and real exponents.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace CubeSections

def ballSincIntegrand (p t : ℝ) : ℝ := |Real.sinc (Real.pi*t)| ^ p

def ballSincIntegral (p : ℝ) : ℝ := ∫ t : ℝ, ballSincIntegrand p t

/-- Integrability, the sharp scalar sinc bound, and its equality exponent. -/
def StrictBallSincBound : Prop :=
  ∀ p : ℝ, 2 ≤ p → Integrable (ballSincIntegrand p) ∧
    ballSincIntegral p ≤ Real.sqrt (2/p) ∧
    (ballSincIntegral p = Real.sqrt (2/p) ↔ p=2)

def scaledSincIntegral (b : ℝ) : ℝ :=
  ∫ t : ℝ, |Real.sinc (Real.pi*Real.sqrt b*t)| ^ (1/b)

def sincProduct {ι : Type*} [Fintype ι] (b : ι → ℝ) : ℝ :=
  ∏ i, scaledSincIntegral (b i) ^ (b i)

theorem ballSincIntegrand_nonneg (p t : ℝ) : 0 ≤ ballSincIntegrand p t :=
  Real.rpow_nonneg (abs_nonneg _) _

theorem continuous_ballSincIntegrand (p : ℝ) (hp : 0 ≤ p) :
    Continuous (ballSincIntegrand p) := by
  exact ((Real.continuous_sinc.comp (continuous_const.mul continuous_id)).abs).rpow_const
    (fun _ => Or.inr hp)

theorem ballSincIntegral_pos (p : ℝ) (hp : 0 ≤ p)
    (hint : Integrable (ballSincIntegrand p)) : 0 < ballSincIntegral p := by
  apply integral_pos_of_integrable_nonneg_ne_zero (continuous_ballSincIntegrand p hp) hint
    (ballSincIntegrand_nonneg p)
  show ballSincIntegrand p 0 ≠ 0
  simp [ballSincIntegrand]

theorem scaledSincIntegral_eq (b : ℝ) (hb : 0 < b) :
    scaledSincIntegral b = ballSincIntegral (1/b) / Real.sqrt b := by
  have h := Measure.integral_comp_mul_left (ballSincIntegrand (1/b)) (Real.sqrt b)
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  calc
    scaledSincIntegral b = ∫ t : ℝ, ballSincIntegrand (1/b) (Real.sqrt b*t) := by
      simp only [scaledSincIntegral, ballSincIntegrand, mul_assoc]
    _ = |(Real.sqrt b)⁻¹| • ∫ t : ℝ, ballSincIntegrand (1/b) t := h
    _ = ballSincIntegral (1/b) / Real.sqrt b := by
      rw [abs_of_pos (inv_pos.2 hs)]
      simp only [ballSincIntegral, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem reciprocal_ge_two_of_le_half (b : ℝ) (hb : 0 < b) (hb' : b ≤ 1/2) :
    2 ≤ 1/b := by
  apply (le_div_iff₀ hb).2
  linarith

theorem sqrt_ball_scale (b : ℝ) (hb : 0 < b) :
    Real.sqrt (2/(1/b)) = Real.sqrt 2 * Real.sqrt b := by
  have heq : 2/(1/b) = 2*b := by field_simp
  rw [heq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

theorem scaledSincIntegral_pos (hBall : StrictBallSincBound) (b : ℝ)
    (hb : 0 < b) (hb' : b ≤ 1/2) : 0 < scaledSincIntegral b := by
  rw [scaledSincIntegral_eq b hb]
  exact div_pos (ballSincIntegral_pos _ (by positivity)
    (hBall _ (reciprocal_ge_two_of_le_half b hb hb')).1) (Real.sqrt_pos.2 hb)

theorem scaledSincIntegral_le_sqrt_two (hBall : StrictBallSincBound) (b : ℝ)
    (hb : 0 < b) (hb' : b ≤ 1/2) : scaledSincIntegral b ≤ Real.sqrt 2 := by
  rw [scaledSincIntegral_eq b hb]
  apply (div_le_iff₀ (Real.sqrt_pos.2 hb)).2
  exact (hBall _ (reciprocal_ge_two_of_le_half b hb hb')).2.1.trans_eq (sqrt_ball_scale b hb)

theorem scaledSincIntegral_eq_sqrt_two_iff (hBall : StrictBallSincBound) (b : ℝ)
    (hb : 0 < b) (hb' : b ≤ 1/2) :
    scaledSincIntegral b = Real.sqrt 2 ↔ b=1/2 := by
  rw [scaledSincIntegral_eq b hb, div_eq_iff (ne_of_gt (Real.sqrt_pos.2 hb)),
    ← sqrt_ball_scale b hb, (hBall _ (reciprocal_ge_two_of_le_half b hb hb')).2.2]
  constructor
  · intro h
    have := (div_eq_iff (ne_of_gt hb)).1 h
    linarith
  · intro h
    rw [h]
    norm_num

theorem scaledSincIntegral_lt_sqrt_two (hBall : StrictBallSincBound) (b : ℝ)
    (hb : 0 < b) (hb' : b < 1/2) : scaledSincIntegral b < Real.sqrt 2 := by
  refine lt_of_le_of_ne (scaledSincIntegral_le_sqrt_two hBall b hb hb'.le) ?_
  intro heq
  have heqb := (scaledSincIntegral_eq_sqrt_two_iff hBall b hb hb'.le).1 heq
  exact (ne_of_lt hb') heqb

theorem scaledSincFactor_pos (hBall : StrictBallSincBound) (b : ℝ)
    (hb : 0 ≤ b) (hb' : b ≤ 1/2) : 0 < scaledSincIntegral b ^ b := by
  rcases eq_or_lt_of_le hb with h | h
  · rw [← h, Real.rpow_zero]
    norm_num
  · exact Real.rpow_pos_of_pos (scaledSincIntegral_pos hBall b h hb') _

theorem scaledSincFactor_le (hBall : StrictBallSincBound) (b : ℝ)
    (hb : 0 ≤ b) (hb' : b ≤ 1/2) :
    scaledSincIntegral b ^ b ≤ (Real.sqrt 2) ^ b := by
  rcases eq_or_lt_of_le hb with h | h
  · simp [← h]
  · exact Real.rpow_le_rpow (scaledSincIntegral_pos hBall b h hb').le
      (scaledSincIntegral_le_sqrt_two hBall b h hb') hb

theorem sincProduct_le {ι : Type*} [Fintype ι] (hBall : StrictBallSincBound)
    (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hb' : ∀ i, b i ≤ 1/2) :
    sincProduct b ≤ (Real.sqrt 2) ^ (∑ i, b i) := by
  rw [Real.rpow_sum_of_pos (by positivity : 0 < Real.sqrt (2 : ℝ))]
  exact Finset.prod_le_prod₀
    (fun i _ => (scaledSincFactor_pos hBall _ (hb i) (hb' i)).le)
    (fun i _ => scaledSincFactor_le hBall _ (hb i) (hb' i))

theorem sincProduct_lt_of_interior {ι : Type*} [Fintype ι] (hBall : StrictBallSincBound)
    (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hb' : ∀ i, b i ≤ 1/2)
    (hint : ∃ i, 0 < b i ∧ b i < 1/2) :
    sincProduct b < (Real.sqrt 2) ^ (∑ i, b i) := by
  rw [Real.rpow_sum_of_pos (by positivity : 0 < Real.sqrt (2 : ℝ))]
  apply Finset.prod_lt_prod₀
    (fun i _ => scaledSincFactor_pos hBall _ (hb i) (hb' i))
    (fun i _ => scaledSincFactor_le hBall _ (hb i) (hb' i))
  obtain ⟨i, hi, hi'⟩ := hint
  exact ⟨i, Finset.mem_univ i, Real.rpow_lt_rpow
    (scaledSincIntegral_pos hBall _ hi hi'.le).le
    (scaledSincIntegral_lt_sqrt_two hBall _ hi hi') hi⟩

/-- Equality in the finite product forces every positive complementary leverage
to be exactly one half; zero weights are retained with exponent zero. -/
theorem sincProduct_eq_iff {ι : Type*} [Fintype ι] (hBall : StrictBallSincBound)
    (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hb' : ∀ i, b i ≤ 1/2) :
    sincProduct b = (Real.sqrt 2) ^ (∑ i, b i) ↔ ∀ i, b i=0 ∨ b i=1/2 := by
  constructor
  · intro heq i
    by_cases hi : b i=0
    · exact Or.inl hi
    right
    by_contra hhalf
    have hlt := sincProduct_lt_of_interior hBall b hb hb'
      ⟨i, lt_of_le_of_ne (hb i) (Ne.symm hi), lt_of_le_of_ne (hb' i) hhalf⟩
    exact (ne_of_lt hlt) heq
  · intro h
    rw [Real.rpow_sum_of_pos (by positivity : 0 < Real.sqrt (2 : ℝ))]
    apply Finset.prod_congr rfl
    intro i hi
    rcases h i with h | h
    · simp [h]
    · have hscalar := (scaledSincIntegral_eq_sqrt_two_iff hBall (b i)
        (by rw [h]; norm_num) (hb' i)).2 h
      rw [hscalar]

#print axioms sincProduct_eq_iff
end CubeSections
