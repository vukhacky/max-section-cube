import CubeSections.Integer.Packing
import CubeSections.LinearAlgebra.Gram

/-!
# Integer packing of actual Gram projections

The row-replacement and reciprocal-window hypotheses are explicit local
conditions. They are not assumed for arbitrary sections in the main theorem.
-/
noncomputable section
open scoped BigOperators
namespace CubeSections

def RowReplacement {n k : ℕ} (U : Frame n k) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    |leverage U i - leverage U j| ≤ leverage U i * leverage U j - gramProjection U i j ^ 2

def ReciprocalWindow {n k : ℕ} (q : ℕ) (U : Frame n k) : Prop :=
  ∀ i : Fin n, 1 / ((q : ℝ) + 1) ≤ leverage U i ∧ leverage U i ≤ 1 / (q : ℝ)

def gramAngularDefect {n k : ℕ} (U : Frame n k) : ℝ :=
  k - ∑ i : Fin n, ∑ j : Fin n,
    gramProjection U i j ^ 4 / (leverage U i * leverage U j)

def integerDefect {n k : ℕ} (q : ℕ) (U : Frame n k) : ℝ :=
  ∑ i : Fin n, (1 - (q : ℝ) * leverage U i) * (((q : ℝ) + 1) * leverage U i - 1)

def gramPackingRemainder {n k : ℕ} (q : ℕ) (U : Frame n k) : ℝ :=
  ∑ i : Fin n, ((q : ℝ) * leverage U i ^ 2 + (1 - (q : ℝ) * leverage U i) ^ 2 -
    (∑ j : Fin n, gramProjection U i j ^ 4) / leverage U i ^ 2)

def gramMismatchRemainder {n k : ℕ} (U : Frame n k) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
    gramProjection U i j ^ 4 * ((leverage U i)⁻¹ - (leverage U j)⁻¹) ^ 2

theorem reciprocalWindow_pos {n k : ℕ} (q : ℕ) (U : Frame n k)
    (hwin : ReciprocalWindow q U) (i : Fin n) : 0 < leverage U i := by
  have hq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  exact (one_div_pos.mpr hq).trans_le (hwin i).1

theorem reciprocalWindow_mul {n k : ℕ} (q : ℕ) (hq : 1 ≤ q) (U : Frame n k)
    (hwin : ReciprocalWindow q U) (i : Fin n) :
    (q : ℝ) * leverage U i ≤ 1 ∧ 1 ≤ ((q : ℝ) + 1) * leverage U i := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  constructor
  · have h := (le_div_iff₀ hqp).mp (hwin i).2
    simpa only [mul_comm] using h
  · have h := (div_le_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) + 1)).mp (hwin i).1
    simpa only [mul_comm] using h

/-- Replacing either row forces every squared Gram entry below both squared leverages. -/
theorem gram_entry_sq_le_leverage_sq {n k : ℕ} (U : Frame n k)
    (hrep : RowReplacement U) (i j : Fin n) :
    gramProjection U i j ^ 2 ≤ leverage U i ^ 2 := by
  by_cases hij : i = j
  · subst j
    rfl
  have h := hrep i j hij
  have hi0 := leverage_nonneg U i
  have hj0 := leverage_nonneg U j
  have hi1 := leverage_le_one U i
  have hj1 := leverage_le_one U j
  by_cases hle : leverage U i ≤ leverage U j
  · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at h
    have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hle) (sub_nonpos.mpr hi1)
    nlinarith
  · have hle' : leverage U j ≤ leverage U i := le_of_not_ge hle
    rw [abs_of_nonneg (sub_nonneg.mpr hle')] at h
    have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hle') (sub_nonpos.mpr hj1)
    nlinarith

theorem gram_row_fourth_le {n k : ℕ} (q : ℕ) (hq : 1 ≤ q) (U : Frame n k)
    (hrep : RowReplacement U) (hwin : ReciprocalWindow q U) (i : Fin n) :
    (∑ j : Fin n, gramProjection U i j ^ 4) ≤
      (q : ℝ) * leverage U i ^ 4 + (leverage U i - q * leverage U i ^ 2) ^ 2 := by
  have hm := reciprocalWindow_mul q hq U hwin i
  have h := capped_row_sq Finset.univ (fun j => gramProjection U i j ^ 2)
    (leverage U i) (reciprocalWindow_pos q U hwin i)
    (fun j _ => sq_nonneg _) (fun j _ => gram_entry_sq_le_leverage_sq U hrep i j)
    (gramProjection_row_sq_sum U i) q hm.1 hm.2
  simpa only [← pow_mul] using h

/-- Symmetrizing the denominator loss gives its exact squared mismatch. -/
theorem symmetric_fourth_variation {n : ℕ} (P : Fin n → Fin n → ℝ)
    (hP : ∀ i j, P i j = P j i) (z : Fin n → ℝ) :
    (1 / 2 : ℝ) * (∑ i, ∑ j, P i j ^ 4 * (z i - z j) ^ 2) =
      (∑ i, ∑ j, P i j ^ 4 * z i ^ 2) - (∑ i, ∑ j, P i j ^ 4 * z i * z j) := by
  have hswap : (∑ i, ∑ j, P i j ^ 4 * z j ^ 2) = ∑ i, ∑ j, P i j ^ 4 * z i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hP j i]
  have hexp : (∑ i, ∑ j, P i j ^ 4 * (z i - z j) ^ 2) =
      (∑ i, ∑ j, P i j ^ 4 * z i ^ 2) + (∑ i, ∑ j, P i j ^ 4 * z j ^ 2) -
        2 * (∑ i, ∑ j, P i j ^ 4 * z i * z j) := by
    calc
      _ = ∑ i, ∑ j, (P i j ^ 4 * z i ^ 2 + P i j ^ 4 * z j ^ 2 -
          2 * (P i j ^ 4 * z i * z j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hexp, hswap]
  ring

theorem gramMismatchRemainder_identity {n k : ℕ} (U : Frame n k) :
    gramMismatchRemainder U =
      (∑ i : Fin n, (∑ j : Fin n, gramProjection U i j ^ 4) / leverage U i ^ 2) -
      (∑ i : Fin n, ∑ j : Fin n, gramProjection U i j ^ 4 /
        (leverage U i * leverage U j)) := by
  have h := symmetric_fourth_variation (gramProjection U) (gramProjection_symm U)
    (fun i => (leverage U i)⁻¹)
  simpa only [gramMismatchRemainder, div_eq_mul_inv, mul_inv, inv_pow,
    Finset.sum_mul, mul_assoc] using h

/-- Exact nonnegative-remainder decomposition from the manuscript. -/
theorem gramPacking_identity {n k : ℕ} (q : ℕ) (U : Frame n k) :
    gramAngularDefect U = integerDefect q U + gramPackingRemainder q U +
      gramMismatchRemainder U := by
  have hTP : integerDefect q U + gramPackingRemainder q U =
      (k : ℝ) - ∑ i : Fin n, (∑ j : Fin n, gramProjection U i j ^ 4) / leverage U i ^ 2 := by
    unfold integerDefect gramPackingRemainder
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i : Fin n, (leverage U i -
          (∑ j : Fin n, gramProjection U i j ^ 4) / leverage U i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, sum_leverage U]
  rw [hTP, gramMismatchRemainder_identity]
  unfold gramAngularDefect
  ring

theorem gramMismatchRemainder_nonneg {n k : ℕ} (U : Frame n k) :
    0 ≤ gramMismatchRemainder U := by
  unfold gramMismatchRemainder
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  positivity

theorem gramPackingRemainder_nonneg {n k : ℕ} (q : ℕ) (hq : 1 ≤ q) (U : Frame n k)
    (hrep : RowReplacement U) (hwin : ReciprocalWindow q U) :
    0 ≤ gramPackingRemainder q U := by
  apply Finset.sum_nonneg
  intro i hi
  have hc := reciprocalWindow_pos q U hwin i
  have hrow := gram_row_fourth_le q hq U hrep hwin i
  have hdiv : (∑ j : Fin n, gramProjection U i j ^ 4) / leverage U i ^ 2 ≤
      (q : ℝ) * leverage U i ^ 2 + (1 - (q : ℝ) * leverage U i) ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hc)).mpr
    convert hrow using 1 <;> ring
  exact sub_nonneg.mpr hdiv

theorem integerDefect_nonneg {n k : ℕ} (q : ℕ) (hq : 1 ≤ q) (U : Frame n k)
    (hwin : ReciprocalWindow q U) : 0 ≤ integerDefect q U := by
  apply Finset.sum_nonneg
  intro i hi
  have h := reciprocalWindow_mul q hq U hwin i
  exact mul_nonneg (sub_nonneg.mpr h.1) (sub_nonneg.mpr h.2)

/-- Sharp integer packing inequality under the explicit extremal-frame conditions. -/
theorem gramAngularDefect_ge_integerDefect {n k : ℕ} (q : ℕ) (hq : 1 ≤ q) (U : Frame n k)
    (hrep : RowReplacement U) (hwin : ReciprocalWindow q U) :
    integerDefect q U ≤ gramAngularDefect U := by
  rw [gramPacking_identity q U]
  have hP := gramPackingRemainder_nonneg q hq U hrep hwin
  have hH := gramMismatchRemainder_nonneg U
  linarith

end CubeSections
