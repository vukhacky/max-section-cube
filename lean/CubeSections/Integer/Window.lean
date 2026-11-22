import CubeSections.Integer.Target
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Exact target values throughout one integer quotient window. -/
noncomputable section
namespace CubeSections

theorem sharpValue_sq (n k : ℕ) :
    sharpValue n k ^ 2 = ((n / k : ℕ) : ℝ) ^ (k - n % k) *
      ((n / k : ℕ) + 1 : ℝ) ^ (n % k) := by
  unfold sharpValue
  rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  push_cast
  rfl

/-- The endpoint r=k agrees with the next divisible dimension. -/
theorem sharpValue_window (q k r : ℕ) (hk : 1 ≤ k) (hr : r ≤ k) :
    sharpValue (q * k + r) k =
      Real.sqrt ((q : ℝ) ^ (k - r) * ((q : ℝ) + 1) ^ r) := by
  rcases lt_or_eq_of_le hr with hlt | heq
  · have hdiv : (q * k + r) / k = q := by
      rw [Nat.mul_comm q k, Nat.mul_add_div (by omega : 0 < k), Nat.div_eq_of_lt hlt,
        Nat.add_zero]
    have hmod : (q * k + r) % k = r := Nat.mul_add_mod_of_lt hlt
    unfold sharpValue
    rw [hdiv, hmod]
    congr 1
    push_cast
    rfl
  · subst r
    rw [show q * k + k = (q + 1) * k by ring, sharpValue_mul (q + 1) k hk]
    simp only [Nat.sub_self, pow_zero, one_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]

theorem sharpValue_window_sq (q k r : ℕ) (hk : 1 ≤ k) (hr : r ≤ k) :
    sharpValue (q * k + r) k ^ 2 = (q : ℝ) ^ (k - r) * ((q : ℝ) + 1) ^ r := by
  rw [sharpValue_window q k r hk hr, Real.sq_sqrt]
  positivity

/-- Consecutive squared targets have the exact ratio (q+1)/q inside a window. -/
theorem sharpValue_window_step_sq (q k r : ℕ) (hk : 1 ≤ k) (hr : r < k) :
    (q : ℝ) * sharpValue (q * k + (r + 1)) k ^ 2 =
      ((q : ℝ) + 1) * sharpValue (q * k + r) k ^ 2 := by
  rw [sharpValue_window_sq q k (r + 1) hk (by omega),
    sharpValue_window_sq q k r hk (by omega)]
  have he : k - r = (k - (r + 1)) + 1 := by omega
  rw [he, pow_succ, pow_succ]
  ring

/-- Exact neighboring target ratio, including the right divisible endpoint. -/
theorem sharpValue_window_step (q k r : ℕ) (hq : 1 ≤ q) (hk : 1 ≤ k) (hr : r < k) :
    sharpValue (q * k + (r + 1)) k =
      Real.sqrt (((q : ℝ) + 1) / q) * sharpValue (q * k + r) k := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hrat : (0 : ℝ) ≤ ((q : ℝ) + 1) / q := by positivity
  apply (sq_eq_sq₀ (sharpValue_nonneg _ _) (mul_nonneg (Real.sqrt_nonneg _) (sharpValue_nonneg _ _))).mp
  rw [mul_pow, Real.sq_sqrt hrat]
  apply (mul_left_cancel₀ (ne_of_gt hqp))
  calc
    (q : ℝ) * sharpValue (q * k + (r + 1)) k ^ 2 =
      ((q : ℝ) + 1) * sharpValue (q * k + r) k ^ 2 :=
        sharpValue_window_step_sq q k r hk hr
    _ = (q : ℝ) * ((((q : ℝ) + 1) / q) * sharpValue (q * k + r) k ^ 2) := by
      field_simp

/-- Neighboring target formula expressed directly in terms of n and k. -/
theorem sharpValue_succ {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    sharpValue (n + 1) k =
      Real.sqrt ((((n / k : ℕ) : ℝ) + 1) / ((n / k : ℕ) : ℝ)) * sharpValue n k := by
  have h := sharpValue_window_step (n / k) k (n % k) (quotient_pos hk hkn) hk
    (remainder_lt hk)
  have hn := quotient_remainder n k
  have hn1 : (n / k) * k + (n % k + 1) = n + 1 := by omega
  rw [hn1, ← hn] at h
  exact h

theorem sharpValue_succ_ratio {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    sharpValue (n + 1) k / sharpValue n k =
      Real.sqrt ((((n / k : ℕ) : ℝ) + 1) / ((n / k : ℕ) : ℝ)) := by
  rw [sharpValue_succ hk hkn]
  exact mul_div_cancel_right₀ _ (ne_of_gt (sharpValue_pos hk hkn))

/-- The deletion ratio inside an integer window, with its left endpoint included. -/
theorem sharpValue_window_prev (q k r : ℕ) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hr0 : 1 ≤ r) (hr : r ≤ k) :
    sharpValue (q * k + (r - 1)) k =
      Real.sqrt ((q : ℝ) / ((q : ℝ) + 1)) * sharpValue (q * k + r) k := by
  have hqp : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hrat : (0 : ℝ) ≤ (q : ℝ) / ((q : ℝ) + 1) := by positivity
  have hstep := sharpValue_window_step_sq q k (r - 1) hk (by omega)
  rw [Nat.sub_add_cancel hr0] at hstep
  apply (sq_eq_sq₀ (sharpValue_nonneg _ _) (mul_nonneg (Real.sqrt_nonneg _) (sharpValue_nonneg _ _))).mp
  rw [mul_pow, Real.sq_sqrt hrat]
  apply (mul_left_cancel₀ (ne_of_gt hqp))
  calc
    ((q : ℝ) + 1) * sharpValue (q * k + (r - 1)) k ^ 2 =
      (q : ℝ) * sharpValue (q * k + r) k ^ 2 := hstep.symm
    _ = ((q : ℝ) + 1) * (((q : ℝ) / ((q : ℝ) + 1)) *
        sharpValue (q * k + r) k ^ 2) := by field_simp

end CubeSections
