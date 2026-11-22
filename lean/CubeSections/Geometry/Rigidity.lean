import CubeSections.Geometry.SignedBlocks
import CubeSections.Geometry.RowSupport
import CubeSections.Integer.GramAngular
import CubeSections.Integer.Target

/-! Row replacement and positivity remain explicit in zero-angular rigidity. -/
noncomputable section
open Set
namespace CubeSections

theorem rowsOrthogonalOrSigned_of_rowReplacement_zeroAngular {n k : ℕ}
    (U : Frame n k) (hrep : RowReplacement U) (hzero : gramAngularDefect U = 0) :
    RowsOrthogonalOrSigned U := by
  intro i j
  rcases (gramAngularDefect_eq_zero_iff U).mp hzero i j with horth | hpar
  · left
    exact (inner_rowVector_rowVector U i j).trans horth
  · have hc : leverage U i = leverage U j := by
      by_cases hij : i = j
      · rw [hij]
      · have h := hrep i j hij
        rw [hpar, sub_self] at h
        exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
    rcases frameRows_eq_or_eq_neg_of_equal_leverage U i j hc hpar with h | h
    · right; left
      ext a
      exact congrFun h a
    · right; right
      ext a
      exact congrFun h a

theorem exists_windowBlockData_of_rowReplacement_zeroAngular {n k : ℕ}
    (q : ℕ) (hq : 1 ≤ q) (U : Frame n k) (hrep : RowReplacement U)
    (hwin : ReciprocalWindow q U) (hzero : gramAngularDefect U = 0) :
    ∃ d : BlockData n k, Set.range U = d.plane ∧
      ∀ j : Fin k, d.blockSize j = q ∨ d.blockSize j = q + 1 := by
  obtain ⟨d, hrange, hweight⟩ := exists_signedBlockData U
    (reciprocalWindow_pos q U hwin)
    (rowsOrthogonalOrSigned_of_rowReplacement_zeroAngular U hrep hzero)
  refine ⟨d, hrange, ?_⟩
  intro j
  obtain ⟨i, hi⟩ := d.onto j
  have hc := reciprocalWindow_pos q U hwin i
  have hm := reciprocalWindow_mul q hq U hwin i
  have hw := hweight i
  rw [hi] at hw
  have hlo : (q : ℝ) ≤ d.blockSize j := by
    apply (mul_le_mul_iff_left₀ hc).mp
    rw [hw]
    exact hm.1
  have hhi : (d.blockSize j : ℝ) ≤ (q : ℝ) + 1 := by
    apply (mul_le_mul_iff_left₀ hc).mp
    rw [hw]
    exact hm.2
  have hloN : q ≤ d.blockSize j := by exact_mod_cast hlo
  have hhiN : d.blockSize j ≤ q + 1 := by exact_mod_cast hhi
  omega

theorem isBalancedSection_of_rowReplacement_zeroAngular {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (U : Frame n k) (hrep : RowReplacement U)
    (hwin : ReciprocalWindow (n / k) U) (hzero : gramAngularDefect U = 0) :
    IsBalancedSection U := by
  obtain ⟨d, hrange, hbalanced⟩ :=
    exists_windowBlockData_of_rowReplacement_zeroAngular (n / k)
      (quotient_pos hk hkn) U hrep hwin hzero
  exact ⟨d, hbalanced, hrange⟩
end CubeSections
