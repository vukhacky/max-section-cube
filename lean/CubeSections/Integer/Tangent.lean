import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! The integer tangent bound, retaining negative integer exponents explicitly. -/
noncomputable section
open scoped BigOperators
namespace CubeSections

theorem tangent_above (q : ℝ) (hq : 0 < q) (m : ℕ) :
    q + (m : ℝ) ≤ q * (1 + 1 / q) ^ m := by
  have hqinv : (0 : ℝ) < 1 / q := by positivity
  have hb := one_add_mul_le_pow (a := (1 / q : ℝ)) (by linarith : (-2 : ℝ) ≤ 1 / q) m
  calc
    q + (m : ℝ) = q * (1 + (m : ℝ) * (1 / q)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hq.le

theorem tangent_below (q : ℝ) (hq : 0 < q) (m : ℕ) :
    (q - (m : ℝ)) * (1 + 1 / q) ^ m ≤ q := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hbpos : (0 : ℝ) < 1 + 1 / q := by positivity
      have hstep : (q - ((m : ℝ) + 1)) * (1 + 1 / q) ≤ q - (m : ℝ) := by
        have hdiv : (q - ((m : ℝ) + 1)) / q ≤ 1 :=
          (div_le_one hq).mpr (by have hm := Nat.cast_nonneg (α := ℝ) m; linarith)
        calc
          _ = (q - ((m : ℝ) + 1)) + (q - ((m : ℝ) + 1)) / q := by ring
          _ ≤ _ := by linarith
      rw [Nat.cast_succ, pow_succ]
      calc
        (q - ((m : ℝ) + 1)) * ((1 + 1 / q) ^ m * (1 + 1 / q)) =
            ((q - ((m : ℝ) + 1)) * (1 + 1 / q)) * (1 + 1 / q) ^ m := by ring
        _ ≤ (q - (m : ℝ)) * (1 + 1 / q) ^ m :=
          mul_le_mul_of_nonneg_right hstep (pow_nonneg hbpos.le _)
        _ ≤ q := ih

/-- Integer tangent inequality, valid also below q because the exponent is an integer. -/
theorem integer_tangent (q b : ℕ) (hq : 1 ≤ q) :
    (b : ℝ) ≤ (q : ℝ) * (1 + 1 / (q : ℝ)) ^ ((b : ℤ) - (q : ℤ)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hbpos : (0 : ℝ) < 1 + 1 / (q : ℝ) := by positivity
  rcases le_total q b with hqb | hbq
  · have hz : (b : ℤ) - (q : ℤ) = ((b - q : ℕ) : ℤ) := by omega
    rw [hz, zpow_natCast]
    have h := tangent_above (q : ℝ) hqpos (b - q)
    rw [Nat.cast_sub hqb] at h
    convert h using 1 <;> ring
  · have hz : (b : ℤ) - (q : ℤ) = -((q - b : ℕ) : ℤ) := by omega
    rw [hz, zpow_neg, zpow_natCast, ← div_eq_mul_inv]
    have h := tangent_below (q : ℝ) hqpos (q - b)
    rw [Nat.cast_sub hbq] at h
    apply (le_div_iff₀ (pow_pos hbpos _)).mpr
    convert h using 1 <;> ring

/-- Products of arbitrary integer powers can be combined when the base is nonzero. -/
theorem prod_zpow_exponents {ι : Type*} (s : Finset ι) (a : ℝ) (ha : a ≠ 0) (z : ι → ℤ) :
    (∏ i ∈ s, a ^ z i) = a ^ (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ ha]

/-- Product version used to compare the target in a lower-dimensional fiber. -/
theorem prod_integer_tangent (q d : ℕ) (hq : 1 ≤ q) (s : Fin d → ℕ) :
    ((∏ j, s j : ℕ) : ℝ) ≤ (q : ℝ) ^ d *
      (1 + 1 / (q : ℝ)) ^ (((∑ j, s j : ℕ) : ℤ) - (q : ℤ) * (d : ℤ)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hbpos : (0 : ℝ) < 1 + 1 / (q : ℝ) := by positivity
  calc
    ((∏ j, s j : ℕ) : ℝ) = ∏ j, (s j : ℝ) := by simp only [Nat.cast_prod]
    _ ≤ ∏ j : Fin d, ((q : ℝ) * (1 + 1 / (q : ℝ)) ^ ((s j : ℤ) - (q : ℤ))) :=
      Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => integer_tangent q (s j) hq)
    _ = (q : ℝ) ^ d * (1 + 1 / (q : ℝ)) ^ (∑ j : Fin d, ((s j : ℤ) - (q : ℤ))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        prod_zpow_exponents _ _ (ne_of_gt hbpos)]
    _ = _ := by
      congr 2
      simp only [Finset.sum_sub_distrib, Nat.cast_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end CubeSections
