import CubeSections.Geometry.Variational
import CubeSections.Integer.GramPacking
import CubeSections.Integer.Window

/-! Reciprocal leverage bounds derived from actual volume-ratio maximality
over an integer window. No row is discarded from the public input. -/
noncomputable section
namespace CubeSections

def RatioMaximalOnWindow {n k : ℕ} (q : ℕ) (U : Frame n k) : Prop :=
  ∀ m : ℕ, q * k ≤ m → m ≤ (q + 1) * k → ∀ V : Frame m k,
    sectionVolume V / sharpValue m k ≤ sectionVolume U / sharpValue n k

theorem duplicate_ratio_le_forces_leverage_upper {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (U : Frame n k) (i : Fin n)
    (hmax : ∀ V : Frame (n + 1) k,
      sectionVolume V / sharpValue (n + 1) k ≤ sectionVolume U / sharpValue n k) :
    leverage U i ≤ 1 / ((n / k : ℕ) : ℝ) := by
  have hW := sharpValue_pos hk hkn
  have hW' := sharpValue_pos hk (by omega : k ≤ n + 1)
  have hV := sectionVolume_pos U
  have h := hmax (normalizedFrame (duplicateRowMap U i) (duplicateRowMap_injective U i))
  rw [duplicateRow_normalized_volume] at h
  have hc := (div_le_div_iff₀ hW' hW).mp h
  have hstep : Real.sqrt (1 + leverage U i) * sharpValue n k ≤ sharpValue (n + 1) k := by
    nlinarith
  rw [sharpValue_succ hk hkn] at hstep
  have hs := (mul_le_mul_iff_left₀ hW).mp hstep
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mpr hs
  have hq : (0 : ℝ) < ((n / k : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n / k from lt_of_lt_of_le Nat.zero_lt_one (quotient_pos hk hkn))
  rw [Real.sq_sqrt (by have := leverage_nonneg U i; linarith),
    Real.sq_sqrt (by positivity)] at hsq
  have hquot : ((((n / k : ℕ) : ℝ) + 1) / ((n / k : ℕ) : ℝ)) =
      1 + 1 / ((n / k : ℕ) : ℝ) := by field_simp
  rw [hquot] at hsq
  linarith

theorem delete_ratio_le_forces_leverage_lower {n k : ℕ}
    (q : ℕ) (hq : 1 ≤ q) (hk : 1 ≤ k) (hkn : k ≤ n)
    (U : Frame (n + 1) k) (i : Fin (n + 1)) (hi : leverage U i < 1)
    (hprev : sharpValue n k = Real.sqrt ((q : ℝ) / ((q : ℝ) + 1)) * sharpValue (n + 1) k)
    (hmax : ∀ V : Frame n k,
      sectionVolume V / sharpValue n k ≤ sectionVolume U / sharpValue (n + 1) k) :
    1 / ((q : ℝ) + 1) ≤ leverage U i := by
  have hW := sharpValue_pos hk hkn
  have hW' := sharpValue_pos hk (by omega : k ≤ n + 1)
  have hV := sectionVolume_pos U
  let D := normalizedFrame (deleteRowMap U i) (deleteRowMap_injective U i hi)
  have hlower := deleteRow_normalized_volume_lower U i hi
  have hc := (div_le_div_iff₀ hW hW').mp (hmax D)
  have hl := mul_le_mul_of_nonneg_right hlower hW'.le
  have hstep : Real.sqrt (1 - leverage U i) * sharpValue (n + 1) k ≤ sharpValue n k := by
    change sectionVolume D * sharpValue (n + 1) k ≤ sectionVolume U * sharpValue n k at hc
    change Real.sqrt (1 - leverage U i) * sectionVolume U * sharpValue (n + 1) k ≤
      sectionVolume D * sharpValue (n + 1) k at hl
    nlinarith
  rw [hprev] at hstep
  have hs := (mul_le_mul_iff_left₀ hW').mp hstep
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mpr hs
  rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by positivity)] at hsq
  have hquot : (q : ℝ) / ((q : ℝ) + 1) = 1 - 1 / ((q : ℝ) + 1) := by
    have hp : (q : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [hquot] at hsq
  linarith

theorem reciprocalWindow_of_ratio_maximal {n k : ℕ}
    (q : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k) (U : Frame n k)
    (hlo : q * k < n) (hhi : n < (q + 1) * k)
    (hmax : RatioMaximalOnWindow q U) : ReciprocalWindow q U := by
  have hkn : k ≤ n := by nlinarith
  have hn : 0 < n := by omega
  cases n with
  | zero => omega
  | succ n =>
    have hkn0 : k ≤ n := by nlinarith
    have hqfloor : (n + 1) / k = q := by
      have hlo' : q ≤ (n + 1) / k := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
      have hhi' : (n + 1) / k < q + 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hhi
      omega
    have hup (i : Fin (n + 1)) : leverage U i ≤ 1 / (q : ℝ) := by
      have h := duplicate_ratio_le_forces_leverage_upper hk hkn U i
        (hmax (n + 2) (by omega) (by omega))
      simpa only [hqfloor] using h
    have hqR : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
    have hlt : 1 / (q : ℝ) < 1 := (div_lt_one (by linarith)).mpr hqR
    have hnrep : n + 1 = q * k + (n + 1) % k := by
      simpa only [hqfloor] using quotient_remainder (n + 1) k
    have hrpos : 1 ≤ (n + 1) % k := by omega
    have hprev := sharpValue_window_prev q k ((n + 1) % k) (by omega) hk hrpos
      (remainder_lt hk).le
    have hnprev : q * k + ((n + 1) % k - 1) = n := by omega
    rw [hnprev, ← hnrep] at hprev
    intro i
    exact ⟨delete_ratio_le_forces_leverage_lower q (by omega) hk hkn0 U i
      ((hup i).trans_lt hlt) hprev (hmax n (by omega) (by omega)), hup i⟩

theorem rowReplacement_of_ratio_maximal {n k : ℕ}
    (q : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k) (U : Frame n k)
    (hlo : q * k < n) (hhi : n < (q + 1) * k)
    (hmax : RatioMaximalOnWindow q U) : RowReplacement U := by
  have hkn : k ≤ n := by nlinarith
  have hW := sharpValue_pos hk hkn
  have hm : IsMaximizingFrame U := by
    intro V
    exact (div_le_div_iff_of_pos_right hW).mp (hmax n hlo.le hhi.le V)
  have hwin := reciprocalWindow_of_ratio_maximal q hq hk U hlo hhi hmax
  have hqR : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hlt : 1 / (q : ℝ) < 1 := (div_lt_one (by linarith)).mpr hqR
  intro i j hij
  exact maximizing_leverage_gap U hm i j ((hwin i).2.trans_lt hlt) ((hwin j).2.trans_lt hlt)

end CubeSections
