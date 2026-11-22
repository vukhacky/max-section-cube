import CubeSections.Integer.Tangent
import CubeSections.Integer.Balanced
import CubeSections.Integer.Window
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact balanced-target comparison for fibers of codimension two. -/
noncomputable section
open scoped BigOperators
namespace CubeSections

theorem sharpValue_sq_le_integer_tangent (q N h : ℕ) (hq : 1 ≤ q)
    (hh : 1 ≤ h) (_hhN : h ≤ N) (hqN : q * h ≤ N) :
    sharpValue N h ^ 2 ≤ (q : ℝ) ^ h * (1 + 1 / (q : ℝ)) ^ (N - q * h) := by
  have ht := prod_integer_tangent q h hq (balancedSizes N h)
  have hs := sum_balancedSizes (n := N) hh
  have hp := prod_of_balanced (balancedSizes N h) hs (balancedSizes_balanced N h)
  rw [hs, hp] at ht
  have hexp : (N : ℤ) - (q : ℤ) * (h : ℤ) = ((N - q * h : ℕ) : ℤ) := by omega
  rw [hexp, zpow_natCast] at ht
  simpa only [sharpValue_sq, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using ht

theorem sharpValue_window_sq_factor (q k r : ℕ) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hr : r ≤ k) :
    sharpValue (q * k + r) k ^ 2 = (q : ℝ) ^ k * (1 + 1 / (q : ℝ)) ^ r := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hbase : (q : ℝ) + 1 = (q : ℝ) * (1 + 1 / (q : ℝ)) := by field_simp
  rw [sharpValue_window_sq q k r hk hr, hbase, mul_pow, ← mul_assoc, ← pow_add,
    Nat.sub_add_cancel hr]

/-- The squared target comparison used before coarea, with k=h+2. -/
theorem sharpValue_fiber_ratio_sq (q h r m l : ℕ) (hq : 1 ≤ q) (hh : 1 ≤ h)
    (hr : r ≤ h + 2) (hm : m ≤ q) (hl : l ≤ q) :
    sharpValue (q * (h + 2) + r - m - l) h ^ 2 ≤
      ((1 / (q : ℝ)) ^ 2 * (1 + 1 / (q : ℝ)) ^ (2 * q - m - l)) *
        sharpValue (q * (h + 2) + r) (h + 2) ^ 2 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hb : q * (h + 2) + r = q * h + r + 2 * q := by ring
  have hN : q * h ≤ q * (h + 2) + r - m - l := by omega
  have hhq : h ≤ q * h := by simpa using Nat.mul_le_mul_right h hq
  have hhN := hhq.trans hN
  have hpow : q * (h + 2) + r - m - l - q * h = r + (2 * q - m - l) := by omega
  have ht := sharpValue_sq_le_integer_tangent q (q * (h + 2) + r - m - l) h hq hh hhN hN
  rw [hpow] at ht
  rw [sharpValue_window_sq_factor q (h + 2) r hq (by omega) hr]
  convert ht using 1
  rw [pow_add, pow_add]
  field_simp

/-- The real radius factor in the manuscript's k-2-dimensional fiber estimate. -/
def fiberRadius (q m l : ℕ) : ℝ :=
  (1 / (q : ℝ)) * (1 + 1 / (q : ℝ)) ^ ((q : ℝ) - ((m : ℝ) + (l : ℝ)) / 2)

theorem fiberRadius_pos (q m l : ℕ) (hq : 1 ≤ q) : 0 < fiberRadius q m l := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  unfold fiberRadius
  positivity

theorem fiberRadius_sq (q m l : ℕ) (hq : 1 ≤ q) (hm : m ≤ q) (hl : l ≤ q) :
    fiberRadius q m l ^ 2 =
      (1 / (q : ℝ)) ^ 2 * (1 + 1 / (q : ℝ)) ^ (2 * q - m - l) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hb : (0 : ℝ) < 1 + 1 / (q : ℝ) := by positivity
  have he : (((2 * q - m - l : ℕ) : ℝ)) = 2 * (q : ℝ) - (m : ℝ) - (l : ℝ) := by
    rw [Nat.cast_sub (by omega : l ≤ 2 * q - m), Nat.cast_sub (by omega : m ≤ 2 * q)]
    push_cast
    rfl
  unfold fiberRadius
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hb.le]
  rw [← Real.rpow_natCast, he]
  congr 1
  ring

/-- The exact ratio bound, valid for every positive-dimensional k-2 fiber. -/
theorem sharpValue_fiber_ratio (q h r m l : ℕ) (hq : 1 ≤ q) (hh : 1 ≤ h)
    (hr : r ≤ h + 2) (hm : m ≤ q) (hl : l ≤ q) :
    sharpValue (q * (h + 2) + r - m - l) h /
      sharpValue (q * (h + 2) + r) (h + 2) ≤ fiberRadius q m l := by
  have hkN : h + 2 ≤ q * (h + 2) + r := by nlinarith
  have hW := sharpValue_pos (by omega : 1 ≤ h + 2) hkN
  apply (div_le_iff₀ hW).mpr
  apply (sq_le_sq₀ (sharpValue_nonneg _ _)
    (mul_nonneg (fiberRadius_pos q m l hq).le hW.le)).mp
  rw [mul_pow, fiberRadius_sq q m l hq hm hl]
  exact sharpValue_fiber_ratio_sq q h r m l hq hh hr hm hl

end CubeSections
