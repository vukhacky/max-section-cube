import CubeSections.Semantics
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators
namespace CubeSections

/-- The integer quotient is positive on the dimension range of the main theorem. -/
theorem quotient_pos {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : 1 ≤ n / k := by
  exact (Nat.le_div_iff_mul_le (by omega : 0 < k)).2 (by simpa using hkn)

theorem remainder_lt {n k : ℕ} (hk : 1 ≤ k) : n % k < k :=
  Nat.mod_lt n (by omega)

theorem quotient_remainder (n k : ℕ) : n = (n / k) * k + n % k := by
  simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div n k).symm

theorem sharpValue_pos {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : 0 < sharpValue n k := by
  unfold sharpValue
  apply Real.sqrt_pos.2
  have hq : 0 < n / k := quotient_pos hk hkn
  exact_mod_cast Nat.mul_pos (Nat.pow_pos hq) (Nat.pow_pos (Nat.succ_pos _))

@[simp] theorem sharpValue_one (n : ℕ) : sharpValue n 1 = Real.sqrt (n : ℝ) := by
  simp only [sharpValue, Nat.div_one, Nat.mod_one, Nat.sub_zero, pow_one, pow_zero, mul_one]

@[simp] theorem sharpValue_self {k : ℕ} (hk : 1 ≤ k) : sharpValue k k = 1 := by
  simp only [sharpValue, Nat.div_self (by omega : 0 < k), Nat.mod_self, Nat.sub_zero,
    one_pow, pow_zero, mul_one, Nat.cast_one, Real.sqrt_one]

theorem sharpValue_mul (q k : ℕ) (hk : 1 ≤ k) :
    sharpValue (q * k) k = Real.sqrt ((q ^ k : ℕ) : ℝ) := by
  simp [sharpValue, Nat.mul_div_left q (by omega : 0 < k)]

/-- If all sizes are q or q+1, their sum determines the number of larger sizes. -/
theorem card_large_of_balanced {n k : ℕ} (s : Fin k → ℕ)
    (hsum : ∑ j, s j = n)
    (hbal : ∀ j, s j = n / k ∨ s j = n / k + 1) :
    (Finset.univ.filter (fun j => s j = n / k + 1)).card = n % k := by
  classical
  have hrep (j : Fin k) : s j = n / k + if s j = n / k + 1 then 1 else 0 := by
    rcases hbal j with h | h
    · rw [h]
      simp
    · rw [h]
      simp
  have hn : n = k * (n / k) + (Finset.univ.filter (fun j => s j = n / k + 1)).card := by
    calc
      n = ∑ j, s j := hsum.symm
      _ = ∑ j, (n / k + if s j = n / k + 1 then 1 else 0) :=
        Finset.sum_congr rfl (fun j _ => hrep j)
      _ = _ := by simp [Finset.sum_add_distrib]
  have hdiv := Nat.mod_add_div n k
  omega

/-- Product of integer sizes of a balanced partition, including all endpoint cases. -/
theorem prod_of_balanced {n k : ℕ} (s : Fin k → ℕ)
    (hsum : ∑ j, s j = n)
    (hbal : ∀ j, s j = n / k ∨ s j = n / k + 1) :
    (∏ j, s j) = (n / k) ^ (k - n % k) * (n / k + 1) ^ (n % k) := by
  classical
  have hc := card_large_of_balanced s hsum hbal
  have hrep (j : Fin k) : s j = if s j = n / k + 1 then n / k + 1 else n / k := by
    rcases hbal j with h | h <;> simp [h]
  calc
    (∏ j, s j) = ∏ j, (if s j = n / k + 1 then n / k + 1 else n / k) :=
      Finset.prod_congr rfl (fun j _ => hrep j)
    _ = (n / k + 1) ^ (Finset.univ.filter (fun j => s j = n / k + 1)).card *
        (n / k) ^ (Finset.univ.filter (fun j => ¬ s j = n / k + 1)).card := by
      rw [Finset.prod_ite]
      simp
    _ = (n / k) ^ (k - n % k) * (n / k + 1) ^ (n % k) := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
        Fintype.card_fin, hc]
      exact Nat.mul_comm _ _

end CubeSections
