import CubeSections.Classical.BallScalarReduction
import CubeSections.Classical.CodimensionRigidity
import CubeSections.Geometry.Endpoints

/-! The independent classical deletion induction and equality reduction.
The analytic hypotheses are genuine sinc-integral statements. No classical
upper bound or main extremal theorem is used to prove its own reduction.
-/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CubeSections

/-- The Fourier-inversion and functional-BL bound relating central section volume
to the product of the scalar sinc integrals. -/
def ClassicalFourierProductBound : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → k ≤ n → n ≤ 2*k → ∀ U : Frame n k,
    (∀ i, 1/2 ≤ leverage U i) →
    sectionVolume U ≤ sincProduct (fun i => 1-leverage U i)

theorem sharpValue_classical {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k) :
    sharpValue n k = (Real.sqrt 2) ^ ((n-k : ℕ) : ℝ) := by
  have h := sharpValue_window 1 k (n-k) hk (by omega)
  have hn' : 1*k+(n-k) = n := by omega
  rw [hn'] at h
  norm_num at h
  rw [h, Real.rpow_natCast]
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)).1
  rw [Real.sq_sqrt (by positivity), ← pow_mul, Nat.mul_comm (n-k) 2, pow_mul,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem sum_complementaryLeverage {n k : ℕ} (hkn : k ≤ n) (U : Frame n k) :
    (∑ i : Fin n, (1-leverage U i)) = ((n-k : ℕ) : ℝ) := by
  rw [Finset.sum_sub_distrib, sum_leverage, Nat.cast_sub hkn]
  simp

theorem sectionVolume_le_sharp_of_half_leverage
    (hBall : StrictBallSincBound) (hFourier : ClassicalFourierProductBound)
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k)
    (U : Frame n k) (hc : ∀ i, 1/2 ≤ leverage U i) :
    sectionVolume U ≤ sharpValue n k := by
  calc
    sectionVolume U ≤ sincProduct (fun i => 1-leverage U i) := hFourier n k hk hkn hn U hc
    _ ≤ (Real.sqrt 2) ^ (∑ i : Fin n, (1-leverage U i)) := sincProduct_le hBall _
      (fun i => sub_nonneg.2 (leverage_le_one U i)) (fun i => by have := hc i; linarith)
    _ = sharpValue n k := by rw [sum_complementaryLeverage hkn U, sharpValue_classical hk hkn hn]

theorem classical_target_step {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n+1 ≤ 2*k) :
    sharpValue (n+1) k ^ 2 = 2 * sharpValue n k ^ 2 := by
  have hq : n/k=1 := Nat.div_eq_of_lt_le (by simpa using hkn) (by omega)
  rw [sharpValue_succ hk hkn, hq]
  norm_num only [Nat.cast_one, one_add_one_eq_two, div_one, mul_pow]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- A complementary leverage greater than one half gives a strict deficit
as soon as the preceding ambient dimension has the codimension bound. -/
theorem sectionVolume_lt_sharp_of_small_leverage {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n+1 ≤ 2*k) (U : Frame (n+1) k)
    (hprev : ∀ V : Frame n k, sectionVolume V ≤ sharpValue n k)
    (i : Fin (n+1)) (hi : leverage U i < 1/2) :
    sectionVolume U < sharpValue (n+1) k := by
  have hi' : leverage U i < 1 := by linarith
  have hlow := deleteRow_normalized_volume_lower U i hi'
  have hprev' := hprev (normalizedFrame (deleteRowMap U i) (deleteRowMap_injective U i hi'))
  have hbound := hlow.trans hprev'
  have hs : 0 ≤ Real.sqrt (1-leverage U i)*sectionVolume U :=
    mul_nonneg (Real.sqrt_nonneg _) (sectionVolume_pos U).le
  have hsq := (sq_le_sq₀ hs (sharpValue_nonneg n k)).2 hbound
  rw [mul_pow, Real.sq_sqrt (sub_nonneg.2 (leverage_le_one U i))] at hsq
  have hstep := classical_target_step hk hkn hn
  have hvpos := sectionVolume_pos U
  have hsqpos := sq_pos_of_pos hvpos
  have hstrict : sectionVolume U ^ 2 < sharpValue (n+1) k ^ 2 := by
    nlinarith
  exact (sq_lt_sq₀ hvpos.le (sharpValue_nonneg _ _)).1 hstrict

/-- Strong induction in the ambient dimension, with full-dimensional base
and deletion for large complementary rows. All sinc inputs are explicit. -/
theorem classical_codimension_bound_of_analytic_inputs
    (hBall : StrictBallSincBound) (hFourier : ClassicalFourierProductBound)
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases heq : n=k
    · subst n
      exact (fullDimension_sectionVolume_eq_sharp U (by omega)).le
    have hlt : k < n := lt_of_le_of_ne hkn (Ne.symm heq)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    by_cases hall : ∀ i, 1/2 ≤ leverage U i
    · exact sectionVolume_le_sharp_of_half_leverage hBall hFourier hk hkn hn U hall
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      exact (sectionVolume_lt_sharp_of_small_leverage hk (by omega) hn U
        (fun V => ih m (by omega) (by omega) (by omega) V) i hi).le

theorem half_leverage_of_classical_equality
    (hBall : StrictBallSincBound) (hFourier : ClassicalFourierProductBound)
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) (hn : n ≤ 2*k)
    (U : Frame n k) (hvol : sectionVolume U = sharpValue n k) :
    ∀ i, 1/2 ≤ leverage U i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  intro i
  by_contra hi
  have hlt := sectionVolume_lt_sharp_of_small_leverage hk (by omega) hn U
    (fun V => classical_codimension_bound_of_analytic_inputs hBall hFourier m k hk (by omega) (by omega) V)
    i (lt_of_not_ge hi)
  exact (ne_of_lt hlt) hvol

theorem classicalLeverageDichotomy_of_sinc_equality
    (hBall : StrictBallSincBound) (hFourier : ClassicalFourierProductBound)
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k)
    (U : Frame n k) (hhalf : ∀ i, 1/2 ≤ leverage U i)
    (hvol : sectionVolume U = sharpValue n k) : ClassicalLeverageDichotomy U := by
  have hb (i : Fin n) : 0 ≤ 1-leverage U i := sub_nonneg.2 (leverage_le_one U i)
  have hb' (i : Fin n) : 1-leverage U i ≤ 1/2 := by have := hhalf i; linarith
  have hlow := hFourier n k hk hkn hn U hhalf
  rw [hvol, sharpValue_classical hk hkn hn, ← sum_complementaryLeverage hkn U] at hlow
  have heq := le_antisymm (sincProduct_le hBall _ hb hb') hlow
  have hcases := (sincProduct_eq_iff hBall _ hb hb').1 heq
  intro i
  rcases hcases i with h | h
  · right; linarith
  · left; linarith

/-- Full classical equality classification conditional on the three visible
analytic outputs: strict sinc, pointwise Fourier/functional BL, and angular
control by the actual slab deficit. -/
theorem classical_equality_iff_of_analytic_inputs
    (hBall : StrictBallSincBound) (hFourier : ClassicalFourierProductBound)
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k)
    (U : Frame n k) (C : ℝ) (hangular : gramAngularDefect U ≤ C*slabDeficit U) :
    sectionVolume U = sharpValue n k ↔ IsBalancedSection U := by
  constructor
  · intro hvol
    by_cases hnk : n=k
    · subst n
      exact fullDimension_isBalancedSection U (by omega)
    have hhalf := half_leverage_of_classical_equality hBall hFourier hk (by omega) hn U hvol
    have hc := classicalLeverageDichotomy_of_sinc_equality hBall hFourier hk hkn hn U hhalf hvol
    exact isBalancedSection_of_classicalLeverage_equality_angular hk hkn hn U hc hvol C hangular
  · exact sectionVolume_eq_sharp_of_isBalancedSection U

#print axioms classical_codimension_bound_of_analytic_inputs
#print axioms classical_equality_iff_of_analytic_inputs
end CubeSections
