import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Capped finite mass packing

The sharp bound is proved by induction on the number of entries. The two
cases depend on whether the partial sum is above or below the integer q.
No assertion about an unconstructed maximizing configuration is used.
-/
noncomputable section
open scoped BigOperators
namespace CubeSections

/-- Sharp sum-of-squares bound for entries in [0,1] with total in [q,q+1]. -/
theorem sum_sq_le_integer_cap {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    (∀ i ∈ s, 0 ≤ x i) → (∀ i ∈ s, x i ≤ 1) →
    ∀ q : ℕ, (q : ℝ) ≤ ∑ i ∈ s, x i → (∑ i ∈ s, x i) ≤ (q : ℝ) + 1 →
    (∑ i ∈ s, x i ^ 2) ≤ (q : ℝ) + ((∑ i ∈ s, x i) - q) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro h0 h1 q hlo hhi
      simp only [Finset.sum_empty]
      positivity
  | @insert a s ha ih =>
      intro h0 h1 q hlo hhi
      have ha0 := h0 a (Finset.mem_insert_self a s)
      have ha1 := h1 a (Finset.mem_insert_self a s)
      have hs0 : ∀ i ∈ s, 0 ≤ x i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have hs1 : ∀ i ∈ s, x i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      have hsum0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hs0
      simp only [Finset.sum_insert ha] at hlo hhi ⊢
      by_cases hq : (q : ℝ) ≤ ∑ i ∈ s, x i
      · have htail := ih hs0 hs1 q hq (by linarith)
        have hcross := mul_nonneg ha0 (sub_nonneg.mpr hq)
        nlinarith
      · have hqpos : 1 ≤ q := by
          by_contra h
          have hzero : q = 0 := by omega
          subst q
          norm_num at hq
          linarith
        have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
          rw [Nat.cast_sub hqpos, Nat.cast_one]
        have hlo' : ((q - 1 : ℕ) : ℝ) ≤ ∑ i ∈ s, x i := by
          rw [hcast]
          linarith
        have hhi' : (∑ i ∈ s, x i) ≤ ((q - 1 : ℕ) : ℝ) + 1 := by
          rw [hcast]
          linarith
        have htail := ih hs0 hs1 (q - 1) hlo' hhi'
        rw [hcast] at htail
        have hcross : 0 ≤ (1 - x a) * ((q : ℝ) - ∑ i ∈ s, x i) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith

/-- The same sharp packing inequality with an arbitrary positive cap. -/
theorem sum_sq_le_cap {ι : Type*} (s : Finset ι) (x : ι → ℝ) (B : ℝ) (hB : 0 < B)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ B)
    (q : ℕ) (hlo : (q : ℝ) * B ≤ ∑ i ∈ s, x i)
    (hhi : (∑ i ∈ s, x i) ≤ ((q : ℝ) + 1) * B) :
    (∑ i ∈ s, x i ^ 2) ≤ (q : ℝ) * B ^ 2 + ((∑ i ∈ s, x i) - q * B) ^ 2 := by
  have h := sum_sq_le_integer_cap s (fun i => x i / B)
    (fun i hi => div_nonneg (h0 i hi) hB.le)
    (fun i hi => (div_le_one hB).mpr (h1 i hi)) q
    (by rw [← Finset.sum_div]; exact (le_div_iff₀ hB).mpr hlo)
    (by rw [← Finset.sum_div]; exact (div_le_iff₀ hB).mpr hhi)
  simp_rw [div_pow] at h
  rw [← Finset.sum_div, ← Finset.sum_div] at h
  calc
    (∑ i ∈ s, x i ^ 2) = ((∑ i ∈ s, x i ^ 2) / B ^ 2) * B ^ 2 := by
      field_simp [ne_of_gt hB]
    _ ≤ ((q : ℝ) + ((∑ i ∈ s, x i) / B - q) ^ 2) * B ^ 2 :=
      mul_le_mul_of_nonneg_right h (sq_nonneg B)
    _ = (q : ℝ) * B ^ 2 + ((∑ i ∈ s, x i) - q * B) ^ 2 := by
      field_simp [ne_of_gt hB]

/-- The packing bound in exactly the scaling used for a squared Gram row. -/
theorem capped_row_sq {ι : Type*} (s : Finset ι) (Y : ι → ℝ) (c : ℝ) (hc : 0 < c)
    (h0 : ∀ i ∈ s, 0 ≤ Y i) (hcap : ∀ i ∈ s, Y i ≤ c ^ 2)
    (hsum : ∑ i ∈ s, Y i = c) (q : ℕ)
    (hlo : (q : ℝ) * c ≤ 1) (hhi : 1 ≤ ((q : ℝ) + 1) * c) :
    (∑ i ∈ s, Y i ^ 2) ≤ (q : ℝ) * c ^ 4 + (c - q * c ^ 2) ^ 2 := by
  have h := sum_sq_le_cap s Y (c ^ 2) (sq_pos_of_pos hc) h0 hcap q
    (by rw [hsum]; nlinarith [mul_le_mul_of_nonneg_right hlo hc.le])
    (by rw [hsum]; nlinarith [mul_le_mul_of_nonneg_right hhi hc.le])
  rw [hsum] at h
  convert h using 1; ring

end CubeSections
