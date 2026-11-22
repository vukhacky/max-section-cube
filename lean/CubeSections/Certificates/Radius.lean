import CubeSections.Certificates.Checker
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace CubeSections.Certificates

/-- The exact real radius factor in the manuscript's two-coordinate fiber bound. -/
def sourceRadius (p : Parameters) : ℝ :=
  (1 / (p.q : ℝ)) * (1 + 1 / (p.q : ℝ)) ^
    ((p.q : ℝ) - ((p.m : ℝ) + (p.l : ℝ)) / 2)

theorem sourceRadius_eq_parity {p : Parameters} (hp : p.Valid) :
    sourceRadius p =
      (1 / (p.q : ℝ)) * (1 + 1 / (p.q : ℝ)) ^ ((2 * p.q - p.m - p.l) / 2) *
        Real.sqrt (1 + 1 / (p.q : ℝ)) ^ ((2 * p.q - p.m - p.l) % 2) := by
  have hq : 2 ≤ p.q := by rcases hp.1 with h | h | h <;> omega
  have hq' : (2 : ℝ) ≤ p.q := by exact_mod_cast hq
  have hmq : p.m ≤ p.q := hp.2.2.1.trans hp.2.2.2
  have hlq : p.l ≤ p.q := hp.2.2.2
  have hm : p.m ≤ 2 * p.q := by omega
  have hl : p.l ≤ 2 * p.q - p.m := by omega
  let N := 2 * p.q - p.m - p.l
  have hN : (N : ℝ) = 2 * (p.q : ℝ) - (p.m : ℝ) - (p.l : ℝ) := by
    dsimp [N]
    simp only [Nat.cast_sub hl, Nat.cast_sub hm, Nat.cast_mul, Nat.cast_ofNat]
  have hsplit : ((N % 2 : ℕ) : ℝ) + 2 * ((N / 2 : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast Nat.mod_add_div N 2
  have hexp : (p.q : ℝ) - ((p.m : ℝ) + (p.l : ℝ)) / 2 =
      ((N / 2 : ℕ) : ℝ) + ((N % 2 : ℕ) : ℝ) / 2 := by
    rw [hN] at hsplit
    linarith
  have hb : (0 : ℝ) < 1 + 1 / (p.q : ℝ) := by positivity
  have hrem : N % 2 = 0 ∨ N % 2 = 1 := by omega
  unfold sourceRadius
  change (1 / (p.q : ℝ)) * (1 + 1 / (p.q : ℝ)) ^
      ((p.q : ℝ) - ((p.m : ℝ) + (p.l : ℝ)) / 2) =
    (1 / (p.q : ℝ)) * (1 + 1 / (p.q : ℝ)) ^ (N / 2) *
      Real.sqrt (1 + 1 / (p.q : ℝ)) ^ (N % 2)
  rw [hexp, Real.rpow_add hb, Real.rpow_natCast]
  rcases hrem with h | h <;> simp [h, Real.sqrt_eq_rpow, mul_assoc]

/-- The exact real factor is bounded by the rational expression used in every leaf. -/
theorem sourceRadius_bounds {p : Parameters} (hp : p.Valid) :
    1 / (p.q : ℝ) ≤ sourceRadius p ∧ sourceRadius p ≤ (radiusUpper p : ℝ) := by
  have hq : 2 ≤ p.q := by rcases hp.1 with h | h | h <;> omega
  have hq' : (2 : ℝ) ≤ p.q := by exact_mod_cast hq
  have hm : (p.m : ℝ) ≤ p.q := by exact_mod_cast hp.2.2.1.trans hp.2.2.2
  have hl : (p.l : ℝ) ≤ p.q := by exact_mod_cast hp.2.2.2
  have hb : (0 : ℝ) < 1 / (p.q : ℝ) := by positivity
  constructor
  · have hpow : (1 : ℝ) ≤ (1 + 1 / (p.q : ℝ)) ^
        ((p.q : ℝ) - ((p.m : ℝ) + (p.l : ℝ)) / 2) :=
      Real.one_le_rpow (by linarith) (by linarith)
    simpa [sourceRadius] using mul_le_mul_of_nonneg_left hpow hb.le
  · rw [sourceRadius_eq_parity hp]
    have hsqrt : Real.sqrt (1 + 1 / (p.q : ℝ)) ≤ 1 + (1 / (p.q : ℝ)) / 2 := by
      apply (Real.sqrt_le_left (by positivity)).mpr
      nlinarith [sq_nonneg (1 / (p.q : ℝ))]
    have hpower := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt ((2 * p.q - p.m - p.l) % 2)
    have hmul := mul_le_mul_of_nonneg_left hpower (show
      (0 : ℝ) ≤ (1 / (p.q : ℝ)) * (1 + 1 / (p.q : ℝ)) ^ ((2 * p.q - p.m - p.l) / 2) by positivity)
    simpa [radiusUpper] using hmul

#print axioms sourceRadius_eq_parity
#print axioms sourceRadius_bounds

end CubeSections.Certificates
