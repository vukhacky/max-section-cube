import CubeSections.Integer.GramPacking
import CubeSections.LinearAlgebra.Projection

/-! Coordinate angular defect, with zero rows retained in every statement. -/
noncomputable section
open scoped BigOperators
namespace CubeSections

def gramPairDefect {n k : ℕ} (U : Frame n k) (i j : Fin n) : ℝ :=
  gramProjection U i j ^ 2 -
    gramProjection U i j ^ 4 / (leverage U i * leverage U j)

theorem gramPairDefect_nonneg {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    0 ≤ gramPairDefect U i j := by
  have hp := gramProjection_entry_sq_le U i j
  have hden : 0 ≤ leverage U i * leverage U j :=
    mul_nonneg (leverage_nonneg U i) (leverage_nonneg U j)
  by_cases hzero : leverage U i * leverage U j = 0
  · simp only [gramPairDefect, hzero, div_zero, sub_zero]
    exact sq_nonneg _
  · have hpos : 0 < leverage U i * leverage U j := lt_of_le_of_ne hden (Ne.symm hzero)
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hpos).mpr
    have h := mul_le_mul_of_nonneg_left hp (sq_nonneg (gramProjection U i j))
    convert h using 1 <;> ring

/-- The coordinate expression agrees with the sum of pairwise angular losses. -/
theorem gramAngularDefect_eq_sum {n k : ℕ} (U : Frame n k) :
    gramAngularDefect U = ∑ i : Fin n, ∑ j : Fin n, gramPairDefect U i j := by
  simp only [gramPairDefect, Finset.sum_sub_distrib]
  simp_rw [gramProjection_row_sq_sum]
  rw [sum_leverage]
  rfl

theorem gramAngularDefect_nonneg {n k : ℕ} (U : Frame n k) :
    0 ≤ gramAngularDefect U := by
  rw [gramAngularDefect_eq_sum]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => gramPairDefect_nonneg U i j))

theorem gramPairDefect_eq_zero_iff {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    gramPairDefect U i j = 0 ↔
      gramProjection U i j = 0 ∨ gramProjection U i j ^ 2 = leverage U i * leverage U j := by
  have hp := gramProjection_entry_sq_le U i j
  by_cases hzero : leverage U i * leverage U j = 0
  · have hP : gramProjection U i j = 0 := by rw [hzero] at hp; nlinarith [sq_nonneg (gramProjection U i j)]
    simp [gramPairDefect, hP]
  · unfold gramPairDefect
    constructor
    · intro h
      have hmul : gramProjection U i j ^ 2 *
          (leverage U i * leverage U j - gramProjection U i j ^ 2) = 0 := by
        have heq : gramProjection U i j ^ 4 /
            (leverage U i * leverage U j) = gramProjection U i j ^ 2 := by linarith
        have heq' := (div_eq_iff hzero).mp heq
        nlinarith
      rcases mul_eq_zero.mp hmul with ha | hb
      · left
        nlinarith [sq_nonneg (gramProjection U i j)]
      · right
        linarith
    · rintro (hP | hP)
      · simp [hP]
      · have hfour : gramProjection U i j ^ 4 =
            (leverage U i * leverage U j) ^ 2 := by nlinarith [sq_nonneg (gramProjection U i j)]
        rw [hP, hfour]
        field_simp
        ring

/-- Zero angular defect is exactly pairwise orthogonality or parallelism of nonzero rows. -/
theorem gramAngularDefect_eq_zero_iff {n k : ℕ} (U : Frame n k) :
    gramAngularDefect U = 0 ↔
      ∀ i j : Fin n, gramProjection U i j = 0 ∨
        gramProjection U i j ^ 2 = leverage U i * leverage U j := by
  rw [gramAngularDefect_eq_sum]
  constructor
  · intro h i j
    have hi : (∑ j : Fin n, gramPairDefect U i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg (fun j _ => gramPairDefect_nonneg U i j))).mp h i
        (Finset.mem_univ i)
    have hij : gramPairDefect U i j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => gramPairDefect_nonneg U i j)).mp hi j
        (Finset.mem_univ j)
    exact (gramPairDefect_eq_zero_iff U i j).mp hij
  · intro h
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    exact (gramPairDefect_eq_zero_iff U i j).mpr (h i j)

end CubeSections
