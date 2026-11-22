import CubeSections.Integer.EntropyQuantization
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Entropy comparison with the continuous target, retaining every zero row.
The geometric volume bound by the slab factor is an explicit separate input. -/
noncomputable section
open scoped BigOperators
namespace CubeSections

theorem slabLogBound_le_continuousTarget {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (U : Frame n k) :
    slabLogBound U ≤ (k : ℝ) / 2 * Real.log ((n : ℝ) / (k : ℝ)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hw : (∑ _i : Fin n, (1 / (n : ℝ))) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hJ := Real.concaveOn_negMulLog.le_map_sum
    (t := Finset.univ) (w := fun _i : Fin n => 1 / (n : ℝ))
    (p := leverage U) (fun _ _ => by positivity) hw
    (fun i _ => leverage_nonneg U i)
  simp only [smul_eq_mul, ← Finset.mul_sum, sum_leverage] at hJ
  have hS : (∑ i : Fin n, Real.negMulLog (leverage U i)) = 2 * slabLogBound U := by
    simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib, slabLogBound]
    ring
  rw [hS] at hJ
  have harg : (1 / (n : ℝ)) * (k : ℝ) = (k : ℝ) / (n : ℝ) := by ring
  rw [harg, Real.negMulLog] at hJ
  have hh := mul_le_mul_of_nonneg_left hJ hnpos.le
  have hl : (n : ℝ) * ((1 / (n : ℝ)) * (2 * slabLogBound U)) = 2 * slabLogBound U := by
    field_simp
  have hr : (n : ℝ) * (-(k : ℝ) / (n : ℝ) * Real.log ((k : ℝ) / (n : ℝ))) =
      (k : ℝ) * Real.log ((n : ℝ) / (k : ℝ)) := by
    rw [Real.log_div (ne_of_gt hkpos) (ne_of_gt hnpos),
      Real.log_div (ne_of_gt hnpos) (ne_of_gt hkpos)]
    field_simp
    ring
  rw [hl] at hh
  have hh' : 2 * slabLogBound U ≤ (k : ℝ) * Real.log ((n : ℝ) / (k : ℝ)) := by
    convert hh using 1
    rw [← hr]
    ring
  linarith

theorem slabBound_le_continuousTarget {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (U : Frame n k) :
    slabBound U ≤ ((n : ℝ) / (k : ℝ)) ^ ((k : ℝ) / 2) := by
  have hp : (0 : ℝ) < (n : ℝ) / (k : ℝ) := by
    exact div_pos (by exact_mod_cast (show 0 < n by omega))
      (by exact_mod_cast (show 0 < k by omega))
  rw [Real.rpow_def_of_pos hp]
  apply Real.exp_le_exp.mpr
  simpa only [mul_comm] using slabLogBound_le_continuousTarget hk hkn U

theorem continuousTarget_at_divisible (q k : ℕ) (hq : 1 ≤ q) (hk : 1 ≤ k) :
    (((q * k : ℕ) : ℝ) / (k : ℝ)) ^ ((k : ℝ) / 2) = sharpValue (q * k) k := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  rw [Nat.cast_mul, mul_div_cancel_right₀ _ hk0, sharpValue_mul q k hk]
  rw [Real.sqrt_eq_rpow, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hqpos.le]
  congr 1
  ring

theorem sectionVolume_le_sharp_divisible_of_slabBound (q k : ℕ)
    (hq : 1 ≤ q) (hk : 1 ≤ k) (U : Frame (q * k) k)
    (hBL : sectionVolume U ≤ slabBound U) :
    sectionVolume U ≤ sharpValue (q * k) k := by
  have hkn : k ≤ q * k := by simpa using Nat.mul_le_mul_right k hq
  have h := hBL.trans (slabBound_le_continuousTarget hk hkn U)
  rwa [continuousTarget_at_divisible q k hq hk] at h

/-- Strict entropy concavity forces uniform leverage, including rows initially equal to zero. -/
theorem leverage_uniform_of_slabLogBound_eq {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (U : Frame n k)
    (heq : slabLogBound U = (k : ℝ) / 2 * Real.log ((n : ℝ) / (k : ℝ))) :
    ∀ i, leverage U i = (k : ℝ) / (n : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hw : (∑ _i : Fin n, (1 / (n : ℝ))) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hS : (∑ i : Fin n, Real.negMulLog (leverage U i)) = 2 * slabLogBound U := by
    simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib, slabLogBound]
    ring
  have hmean : (∑ i : Fin n, (1 / (n : ℝ)) • leverage U i) = (k : ℝ) / (n : ℝ) := by
    simp only [smul_eq_mul, ← Finset.mul_sum, sum_leverage]
    ring
  have hJ : Real.negMulLog (∑ i : Fin n, (1 / (n : ℝ)) • leverage U i) =
      ∑ i : Fin n, (1 / (n : ℝ)) • Real.negMulLog (leverage U i) := by
    rw [hmean]
    simp only [smul_eq_mul, ← Finset.mul_sum]
    rw [hS, heq]
    unfold Real.negMulLog
    rw [Real.log_div (ne_of_gt hkpos) (ne_of_gt hnpos),
      Real.log_div (ne_of_gt hnpos) (ne_of_gt hkpos)]
    ring
  have h := (Real.strictConcaveOn_negMulLog.map_sum_eq_iff
    (t := Finset.univ) (w := fun _i : Fin n => 1 / (n : ℝ)) (p := leverage U)
    (fun _ _ => by positivity) hw (fun i _ => leverage_nonneg U i)).mp hJ
  intro i
  exact (h i (Finset.mem_univ i)).trans hmean

theorem slabLogBound_eq_of_slabBound_eq_continuousTarget {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (U : Frame n k)
    (heq : slabBound U = ((n : ℝ) / (k : ℝ)) ^ ((k : ℝ) / 2)) :
    slabLogBound U = (k : ℝ) / 2 * Real.log ((n : ℝ) / (k : ℝ)) := by
  have hp : (0 : ℝ) < (n : ℝ) / (k : ℝ) := by
    exact div_pos (by exact_mod_cast (show 0 < n by omega))
      (by exact_mod_cast (show 0 < k by omega))
  rw [slabBound, Real.rpow_def_of_pos hp] at heq
  have h := Real.exp_injective heq
  simpa only [mul_comm] using h

theorem leverage_uniform_of_divisible_equality (q k : ℕ)
    (hq : 1 ≤ q) (hk : 1 ≤ k) (U : Frame (q * k) k)
    (hBL : sectionVolume U ≤ slabBound U)
    (heq : sectionVolume U = sharpValue (q * k) k) :
    ∀ i, leverage U i = 1 / (q : ℝ) := by
  have hkn : k ≤ q * k := by simpa using Nat.mul_le_mul_right k hq
  have hB := slabBound_le_continuousTarget hk hkn U
  have hBeq : slabBound U = (((q * k : ℕ) : ℝ) / (k : ℝ)) ^ ((k : ℝ) / 2) := by
    apply le_antisymm hB
    rw [continuousTarget_at_divisible q k hq hk, ← heq]
    exact hBL
  have hu := leverage_uniform_of_slabLogBound_eq hk hkn U
    (slabLogBound_eq_of_slabBound_eq_continuousTarget hk hkn U hBeq)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  intro i
  rw [hu i, Nat.cast_mul]
  field_simp

theorem slabDeficit_zero_of_divisible_equality (q k : ℕ)
    (hq : 1 ≤ q) (hk : 1 ≤ k) (U : Frame (q * k) k)
    (hBL : sectionVolume U ≤ slabBound U)
    (heq : sectionVolume U = sharpValue (q * k) k) : slabDeficit U = 0 := by
  have hkn : k ≤ q * k := by simpa using Nat.mul_le_mul_right k hq
  have hB := slabBound_le_continuousTarget hk hkn U
  rw [continuousTarget_at_divisible q k hq hk, ← heq] at hB
  have hb := le_antisymm hB hBL
  rw [slabDeficit_eq_log_ratio, hb, div_self (ne_of_gt (sectionVolume_pos U)), Real.log_one]

end CubeSections
