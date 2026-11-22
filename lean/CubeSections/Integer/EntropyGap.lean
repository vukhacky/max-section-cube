import CubeSections.Integer.GramPacking
import CubeSections.Integer.Window
import CubeSections.Analysis.SharpEntropy

/-! Exact global entropy gap and the target logarithm. -/
noncomputable section
open scoped BigOperators
namespace CubeSections

/-- Logarithm of the continuous slab Brascamp--Lieb factor. -/
def slabLogBound {n k : ℕ} (U : Frame n k) : ℝ :=
  -(∑ i : Fin n, leverage U i * Real.log (leverage U i)) / 2

/-- The actual logarithmic slab deficit; nonnegativity is proved when used. -/
def slabDeficit {n k : ℕ} (U : Frame n k) : ℝ :=
  slabLogBound U - Real.log (sectionVolume U)

theorem two_mul_log_sharpValue_window (q k r : ℕ) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hr : r ≤ k) :
    2 * Real.log (sharpValue (q * k + r) k) =
      (k : ℝ) * Real.log (q : ℝ) + (r : ℝ) * Real.log (1 + 1 / (q : ℝ)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1pos : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hbasepos : (0 : ℝ) < 1 + 1 / (q : ℝ) := by positivity
  have hbase : (q : ℝ) + 1 = (q : ℝ) * (1 + 1 / (q : ℝ)) := by field_simp
  have hlog : Real.log ((q : ℝ) + 1) =
      Real.log (q : ℝ) + Real.log (1 + 1 / (q : ℝ)) := by
    rw [hbase, Real.log_mul (ne_of_gt hqpos) (ne_of_gt hbasepos)]
  rw [sharpValue_window q k r hk hr, Real.log_sqrt (by positivity),
    Real.log_mul (pow_ne_zero _ (ne_of_gt hqpos)) (pow_ne_zero _ (ne_of_gt hq1pos)),
    Real.log_pow, Real.log_pow, hlog, Nat.cast_sub hr]
  ring

theorem two_mul_log_sharpValue {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    2 * Real.log (sharpValue n k) =
      (k : ℝ) * Real.log ((n / k : ℕ) : ℝ) +
      ((n % k : ℕ) : ℝ) * Real.log (1 + 1 / ((n / k : ℕ) : ℝ)) := by
  have h := two_mul_log_sharpValue_window (n / k) k (n % k) (quotient_pos hk hkn) hk
    (remainder_lt hk).le
  simpa only [← quotient_remainder n k] using h

/-- Sum of the chord contributions equals twice the logarithm of the balanced target. -/
theorem sum_entropy_chord {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (U : Frame n k) :
    (∑ i : Fin n, (leverage U i * Real.log ((n / k : ℕ) : ℝ) +
      (1 - ((n / k : ℕ) : ℝ) * leverage U i) * Real.log (1 + 1 / ((n / k : ℕ) : ℝ)))) =
      2 * Real.log (sharpValue n k) := by
  have hnr : (n : ℝ) - ((n / k : ℕ) : ℝ) * (k : ℝ) = ((n % k : ℕ) : ℝ) := by
    have h : (n : ℝ) = ((n / k : ℕ) : ℝ) * (k : ℝ) + ((n % k : ℕ) : ℝ) := by
      exact_mod_cast quotient_remainder n k
    linarith
  rw [two_mul_log_sharpValue hk hkn]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_leverage U, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, hnr]

/-- The entropy excess has exactly the manuscript's normalization factor two. -/
theorem sum_entropyExcess_eq {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (U : Frame n k)
    (hwin : ReciprocalWindow (n / k) U) :
    (∑ i : Fin n, entropyExcess (n / k) (leverage U i)) =
      2 * (slabLogBound U - Real.log (sharpValue n k)) := by
  have hqpos : (0 : ℝ) < ((n / k : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n / k from quotient_pos hk hkn)
  have hpoint (i : Fin n) : entropyExcess (n / k) (leverage U i) =
      -(leverage U i * Real.log (leverage U i)) -
      (leverage U i * Real.log ((n / k : ℕ) : ℝ) +
        (1 - ((n / k : ℕ) : ℝ) * leverage U i) * Real.log (1 + 1 / ((n / k : ℕ) : ℝ))) := by
    unfold entropyExcess
    rw [Real.log_mul (ne_of_gt hqpos) (ne_of_gt (reciprocalWindow_pos _ U hwin i))]
    ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, sum_entropy_chord hk hkn U]
  unfold slabLogBound
  ring

theorem sum_entropyExcess_le {n k : ℕ} (q : ℕ) (hq : 1 ≤ q) (U : Frame n k)
    (hwin : ReciprocalWindow q U) :
    (∑ i : Fin n, entropyExcess q (leverage U i)) ≤ sharpEntropyCoeff q * integerDefect q U := by
  calc
    _ ≤ ∑ i : Fin n, sharpEntropyCoeff q * reciprocalQuadratic q (leverage U i) :=
      Finset.sum_le_sum (fun i _ => entropyExcess_le_sharpQuadratic q hq _ (hwin i).1 (hwin i).2)
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem sum_entropyExcess_lt_of_interior {n k : ℕ} (q : ℕ) (hq : 1 ≤ q) (U : Frame n k)
    (hwin : ReciprocalWindow q U)
    (hint : ∃ i : Fin n, 1 / ((q : ℝ) + 1) < leverage U i ∧ leverage U i < 1 / (q : ℝ)) :
    (∑ i : Fin n, entropyExcess q (leverage U i)) < sharpEntropyCoeff q * integerDefect q U := by
  have h : (∑ i : Fin n, entropyExcess q (leverage U i)) <
      ∑ i : Fin n, sharpEntropyCoeff q * reciprocalQuadratic q (leverage U i) := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact entropyExcess_le_sharpQuadratic q hq _ (hwin i).1 (hwin i).2
    · obtain ⟨i, hi₀, hi₁⟩ := hint
      exact ⟨i, Finset.mem_univ i, entropyExcess_lt_sharpQuadratic q hq _ hi₀ hi₁⟩
  simpa only [← Finset.mul_sum, reciprocalQuadratic, integerDefect] using h

theorem log_target_ratio {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (U : Frame n k)
    (hwin : ReciprocalWindow (n / k) U) :
    Real.log (sharpValue n k / sectionVolume U) = slabDeficit U -
      (∑ i : Fin n, entropyExcess (n / k) (leverage U i)) / 2 := by
  rw [Real.log_div (ne_of_gt (sharpValue_pos hk hkn)) (ne_of_gt (sectionVolume_pos U)),
    sum_entropyExcess_eq hk hkn U hwin]
  unfold slabDeficit
  ring

end CubeSections
