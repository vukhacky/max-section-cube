import CubeSections.Geometry.Rigidity
import CubeSections.Geometry.BalancedVolume
import CubeSections.Integer.EntropyGap
import CubeSections.Analysis.GlobalTransportEnergy

/-! The geometric end of the classical codimension equality argument.
The sinc/Fourier argument producing the leverage dichotomy and the transport
argument producing zero angular defect remain separate explicit inputs.
-/
noncomputable section
open Set Classical MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CubeSections

def ClassicalLeverageDichotomy {n k : ℕ} (U : Frame n k) : Prop :=
  ∀ i, leverage U i = 1 / 2 ∨ leverage U i = 1

theorem classicalLeverage_pos {n k : ℕ} (U : Frame n k)
    (h : ClassicalLeverageDichotomy U) (i : Fin n) : 0 < leverage U i := by
  rcases h i with hi | hi <;> rw [hi] <;> norm_num

/-- Unit rows cannot be parallel to another row, so no maximality or row
replacement hypothesis is needed in this endpoint rigidity lemma. -/
theorem rowsOrthogonalOrSigned_of_classicalLeverage_zeroAngular {n k : ℕ}
    (U : Frame n k) (hc : ClassicalLeverageDichotomy U)
    (hzero : gramAngularDefect U = 0) : RowsOrthogonalOrSigned U := by
  intro i j
  by_cases hij : i = j
  · subst j
    exact Or.inr (Or.inl rfl)
  rcases (gramAngularDefect_eq_zero_iff U).mp hzero i j with horth | hpar
  · exact Or.inl ((inner_rowVector_rowVector U i j).trans horth)
  have heq : leverage U i = leverage U j := by
    rcases hc i with hi | hi <;> rcases hc j with hj | hj
    · rw [hi, hj]
    · have hz := unit_leverage_offdiag_zero U j i hj (Ne.symm hij)
      rw [gramProjection_symm] at hz
      rw [hz, hi, hj] at hpar
      norm_num at hpar
    · have hz := unit_leverage_offdiag_zero U i j hi hij
      rw [hz, hi, hj] at hpar
      norm_num at hpar
    · rw [hi, hj]
  rcases frameRows_eq_or_eq_neg_of_equal_leverage U i j heq hpar with h | h
  · right; left
    ext a
    exact congrFun h a
  · right; right
    ext a
    exact congrFun h a

theorem exists_classicalBlockData_of_zeroAngular {n k : ℕ}
    (U : Frame n k) (hc : ClassicalLeverageDichotomy U)
    (hzero : gramAngularDefect U = 0) :
    ∃ d : BlockData n k, Set.range U = d.plane ∧
      (∀ j, d.blockSize j = 1 ∨ d.blockSize j = 2) := by
  obtain ⟨d, hrange, hweight⟩ := exists_signedBlockData U
    (classicalLeverage_pos U hc) (rowsOrthogonalOrSigned_of_classicalLeverage_zeroAngular U hc hzero)
  refine ⟨d, hrange, ?_⟩
  intro j
  obtain ⟨i, hi⟩ := d.onto j
  have hw := hweight i
  rw [hi] at hw
  rcases hc i with hh | hh
  · right
    rw [hh] at hw
    have hm : (d.blockSize j : ℝ) = 2 := by linarith
    exact_mod_cast hm
  · left
    rw [hh, mul_one] at hw
    exact_mod_cast hw

theorem classicalBlock_counts {n k : ℕ} (d : BlockData n k)
    (hsize : ∀ j, d.blockSize j = 1 ∨ d.blockSize j = 2) :
    (Finset.univ.filter (fun j => d.blockSize j = 2)).card = n-k ∧
    (Finset.univ.filter (fun j => d.blockSize j = 1)).card = 2*k-n := by
  have heach (j : Fin k) : d.blockSize j = 1 + if d.blockSize j = 2 then 1 else 0 := by
    rcases hsize j with h | h <;> simp [h]
  have hsum : n = k + (Finset.univ.filter (fun j => d.blockSize j = 2)).card := by
    calc
      n = ∑ j : Fin k, d.blockSize j := d.sum_blockSize.symm
      _ = ∑ j : Fin k, (1 + if d.blockSize j = 2 then 1 else 0) :=
        Finset.sum_congr rfl (fun j _ => heach j)
      _ = _ := by simp [Finset.sum_add_distrib]
  have hpartition :
      (Finset.univ.filter (fun j => d.blockSize j = 1)).card +
      (Finset.univ.filter (fun j => d.blockSize j = 2)).card = k := by
    have hnot : (Finset.univ.filter (fun j => d.blockSize j = 1)) =
        Finset.univ.filter (fun j => ¬ d.blockSize j = 2) := by
      ext j
      rcases hsize j with h | h <;> simp [h]
    rw [hnot, Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
    simp only [Finset.card_univ, Fintype.card_fin]
    have hcard := Finset.card_filter_le (s := Finset.univ) (p := fun j : Fin k => d.blockSize j = 2)
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  omega

theorem classicalBlock_isBalanced {n k : ℕ} (hk : 1 ≤ k) (d : BlockData n k)
    (hsize : ∀ j, d.blockSize j = 1 ∨ d.blockSize j = 2) : d.IsBalanced := by
  have hcount := classicalBlock_counts d hsize
  have hlo : k ≤ n := by
    calc
      k = ∑ _j : Fin k, 1 := by simp
      _ ≤ ∑ j : Fin k, d.blockSize j :=
        Finset.sum_le_sum (fun j _ => d.blockSize_pos j)
      _ = n := d.sum_blockSize
  have hhi : n ≤ 2*k := by
    calc
      n = ∑ j : Fin k, d.blockSize j := d.sum_blockSize.symm
      _ ≤ ∑ _j : Fin k, 2 := Finset.sum_le_sum (fun j _ => by rcases hsize j with h | h <;> omega)
      _ = 2*k := by simp [Nat.mul_comm]
  rcases lt_or_eq_of_le hhi with hn | hn
  · have hq : n/k = 1 := Nat.div_eq_of_lt_le (by simpa using hlo) (by simpa using hn)
    intro j
    simpa [hq] using hsize j
  · have hq : n/k = 2 := by rw [hn, Nat.mul_div_left _ (by omega : 0 < k)]
    have hsingle : (Finset.univ.filter (fun j => d.blockSize j = 1)).card = 0 := by
      rw [hcount.2, hn, Nat.sub_self]
    intro j
    left
    rw [hq]
    rcases hsize j with h | h
    · have hj : j ∈ Finset.univ.filter (fun j => d.blockSize j = 1) := by simp [h]
      rw [Finset.card_eq_zero.mp hsingle] at hj
      exact (Finset.notMem_empty j hj).elim
    · exact h

theorem classicalBlock_classification_of_zeroAngular {n k : ℕ}
    (hk : 1 ≤ k) (U : Frame n k) (hc : ClassicalLeverageDichotomy U)
    (hzero : gramAngularDefect U = 0) :
    IsBalancedSection U ∧ sectionVolume U = sharpValue n k ∧
      ∃ d : BlockData n k, Set.range U = d.plane ∧
        (∀ j, d.blockSize j = 1 ∨ d.blockSize j = 2) ∧
        (Finset.univ.filter (fun j => d.blockSize j = 2)).card = n-k ∧
        (Finset.univ.filter (fun j => d.blockSize j = 1)).card = 2*k-n := by
  obtain ⟨d, hrange, hsize⟩ := exists_classicalBlockData_of_zeroAngular U hc hzero
  have hbalanced : IsBalancedSection U := ⟨d, classicalBlock_isBalanced hk d hsize, hrange⟩
  exact ⟨hbalanced, sectionVolume_eq_sharp_of_isBalancedSection U hbalanced,
    d, hrange, hsize, classicalBlock_counts d hsize⟩

theorem slabLogBound_eq_log_sharp_of_classicalLeverage {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k) (U : Frame n k)
    (hc : ClassicalLeverageDichotomy U) :
    slabLogBound U = Real.log (sharpValue n k) := by
  have hpoint (i : Fin n) : leverage U i * Real.log (leverage U i) =
      -(1-leverage U i)*Real.log 2 := by
    rcases hc i with h | h
    · rw [h, Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      simp only [Real.log_one]
      ring
    · simp [h]
  have hsum : (∑ i : Fin n, leverage U i * Real.log (leverage U i)) =
      -((n : ℝ)-(k : ℝ))*Real.log 2 := by
    simp_rw [hpoint]
    rw [← Finset.sum_mul, Finset.sum_neg_distrib, Finset.sum_sub_distrib, sum_leverage]
    simp
  have hlog := two_mul_log_sharpValue_window 1 k (n-k) (by omega) hk (by omega)
  have hn' : 1*k+(n-k) = n := by omega
  rw [hn'] at hlog
  norm_num at hlog
  rw [Nat.cast_sub hkn] at hlog
  unfold slabLogBound
  rw [hsum]
  linarith

theorem slabDeficit_zero_of_classicalLeverage_equality {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k) (U : Frame n k)
    (hc : ClassicalLeverageDichotomy U) (hvol : sectionVolume U = sharpValue n k) :
    slabDeficit U = 0 := by
  rw [slabDeficit, slabLogBound_eq_log_sharp_of_classicalLeverage hk hkn hn U hc, hvol, sub_self]

theorem isBalancedSection_of_classicalLeverage_equality_angular {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k) (U : Frame n k)
    (hc : ClassicalLeverageDichotomy U) (hvol : sectionVolume U = sharpValue n k)
    (C : ℝ) (hangular : gramAngularDefect U ≤ C*slabDeficit U) : IsBalancedSection U := by
  have hδ := slabDeficit_zero_of_classicalLeverage_equality hk hkn hn U hc hvol
  rw [hδ, mul_zero] at hangular
  have hzero := le_antisymm hangular (gramAngularDefect_nonneg U)
  exact (classicalBlock_classification_of_zeroAngular hk U hc hzero).1

/-- A concrete Gaussian energy contract discharges zero angular defect in the
classical equality reduction; existence of this coupling remains explicit. -/
theorem isBalancedSection_of_classicalLeverage_equality_energy {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k) (U : Frame n k)
    (hc : ClassicalLeverageDichotomy U) (hvol : sectionVolume U = sharpValue n k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → E k) (hG : MeasurePreserving G μ (stdGaussian (E k)))
    (β : Fin n → ℝ) (T : Ω → Fin n → ℝ)
    (hE : Integrable (fun ω => frameTransportEnergy U β (T ω) (G ω)) μ)
    (hbound : (∫ ω, frameTransportEnergy U β (T ω) (G ω) ∂μ) ≤ slabDeficit U) :
    IsBalancedSection U := by
  exact isBalancedSection_of_classicalLeverage_equality_angular hk hkn hn U hc hvol 20
    (frame_angular_bound_twenty_of_energy U μ G hG β T (slabDeficit U) hE hbound)

#print axioms classicalBlock_classification_of_zeroAngular
#print axioms isBalancedSection_of_classicalLeverage_equality_energy
end CubeSections
