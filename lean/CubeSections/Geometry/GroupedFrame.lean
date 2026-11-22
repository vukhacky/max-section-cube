import CubeSections.Geometry.CoalescedFrame
import CubeSections.LinearAlgebra.GroupedCharges

/-! Actual class parameters and exact grouped entropy accounting. -/
noncomputable section
open Set Classical
open scoped BigOperators InnerProductSpace
namespace CubeSections

def rowClassAngle {n k : ℕ} (U : Frame n k) (c d : RowClass U) : ℝ :=
  (inner ℝ (rowClassUnit U c) (rowClassUnit U d)) ^ 2

theorem rowClassAngle_nonneg {n k : ℕ} (U : Frame n k) (c d : RowClass U) :
    0 ≤ rowClassAngle U c d := sq_nonneg _

theorem unit_vectors_eq_signed_of_inner_sq_eq_one {k : ℕ} (u v : E k)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (h : (inner ℝ u v) ^ 2 = 1) :
    u = v ∨ u = -v := by
  have hs : (inner ℝ u v) ^ 2 = (1 : ℝ) ^ 2 := by simpa using h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hp | hp
  · left
    have hz : inner ℝ (u - v) (u - v) = 0 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
        real_inner_comm u v, hu, hv, hp]
      norm_num
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  · right
    have hz : inner ℝ (u + v) (u + v) = 0 := by
      rw [inner_add_left, inner_add_right, inner_add_right,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
        real_inner_comm u v, hu, hv, hp]
      norm_num
    exact eq_neg_iff_add_eq_zero.mpr (inner_self_eq_zero.mp hz)

theorem rowClassAngle_lt_one {n k : ℕ} (U : Frame n k) (c d : RowClass U)
    (hcd : c ≠ d) : rowClassAngle U c d < 1 := by
  have hcs := real_inner_mul_inner_self_le (rowClassUnit U c) (rowClassUnit U d)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    rowClassUnit_norm, rowClassUnit_norm] at hcs
  have hle : rowClassAngle U c d ≤ 1 := by simpa [rowClassAngle, pow_two] using hcs
  by_contra hlt
  have heq := le_antisymm hle (le_of_not_gt hlt)
  have hs := unit_vectors_eq_signed_of_inner_sq_eq_one (rowClassUnit U c) (rowClassUnit U d)
    (rowClassUnit_norm U c) (rowClassUnit_norm U d) heq
  have hclasses := (rowClass_eq_iff U (rowClassRep U c) (rowClassRep U d)).mpr hs
  apply hcd
  simpa only [rowClass_rep] using hclasses

theorem classWeight_eq_mass_mul_angle {n k : ℕ} (U : Frame n k)
    (c d : RowClass U) (hcd : c ≠ d) :
    classWeight U c d = rowClassMass U c * rowClassMass U d * rowClassAngle U c d := by
  rw [classWeight, if_neg hcd, classGram_sq]
  rfl

theorem classWeight_pos_ne {n k : ℕ} (U : Frame n k) (c d : RowClass U)
    (hw : 0 < classWeight U c d) : c ≠ d := by
  intro h
  subst d
  simp [classWeight] at hw

theorem rowClassAngle_pos_of_weight_pos {n k : ℕ} (U : Frame n k) (c d : RowClass U)
    (hw : 0 < classWeight U c d) : 0 < rowClassAngle U c d := by
  rw [classWeight_eq_mass_mul_angle U c d (classWeight_pos_ne U c d hw)] at hw
  by_contra h
  have hz := le_antisymm (le_of_not_gt h) (rowClassAngle_nonneg U c d)
  rw [hz, mul_zero] at hw
  exact (lt_irrefl _ hw)

theorem rowClassMass_lt_one_of_weight_pos {n k : ℕ} (U : Frame n k)
    (c d : RowClass U) (hw : 0 < classWeight U c d) : rowClassMass U c < 1 := by
  have hcd := classWeight_pos_ne U c d hw
  have hp : 0 < classGram U c d ^ 2 := by simpa [classWeight, hcd] using hw
  have hb := classGram_complement_bound U c d hcd
  apply lt_of_le_of_ne (rowClassMass_le_one U c)
  intro h
  rw [← h, sub_self, zero_mul] at hb
  exact (not_le_of_gt hp) hb

theorem rowClassLeverage_window {n k : ℕ} (q : ℕ) (U : Frame n k)
    (hwin : ReciprocalWindow q U) (c : RowClass U) :
    1 / ((q : ℝ) + 1) ≤ rowClassLeverage U c ∧
      rowClassLeverage U c ≤ 1 / (q : ℝ) := hwin (rowClassRep U c).val

theorem rowClassMultiplicity_le_of_mass_lt_one {n k : ℕ} (q : ℕ) (hq : 1 ≤ q)
    (U : Frame n k) (hrep : RowReplacement U) (hwin : ReciprocalWindow q U)
    (c : RowClass U) (hc : rowClassMass U c < 1) : rowClassMultiplicity U c ≤ q := by
  have hpos := rowClassLeverage_pos U c
  have hm := (reciprocalWindow_mul q hq U hwin (rowClassRep U c).val).2
  change 1 ≤ ((q : ℝ) + 1) * rowClassLeverage U c at hm
  rw [rowClassMass_eq_multiplicity_mul_leverage U hrep] at hc
  have hmR : (rowClassMultiplicity U c : ℝ) < (q : ℝ) + 1 :=
    (mul_lt_mul_iff_left₀ hpos).mp (hc.trans_le hm)
  have hmN : rowClassMultiplicity U c < q + 1 := by exact_mod_cast hmR
  omega

theorem rowClassMultiplicity_le_of_weight_pos {n k : ℕ} (q : ℕ) (hq : 1 ≤ q)
    (U : Frame n k) (hrep : RowReplacement U) (hwin : ReciprocalWindow q U)
    (c d : RowClass U) (hw : 0 < classWeight U c d) :
    rowClassMultiplicity U c ≤ q ∧ rowClassMultiplicity U d ≤ q := by
  constructor
  · exact rowClassMultiplicity_le_of_mass_lt_one q hq U hrep hwin c
      (rowClassMass_lt_one_of_weight_pos U c d hw)
  · apply rowClassMultiplicity_le_of_mass_lt_one q hq U hrep hwin d
    apply rowClassMass_lt_one_of_weight_pos U d c
    rwa [classWeight_symm]

theorem rowClass_complementary_angle {n k : ℕ} (U : Frame n k)
    (hrep : RowReplacement U) (c d : RowClass U) (hcd : c ≠ d) :
    rowClassAngle U c d ≤
      (1 - (rowClassMultiplicity U c : ℝ) * rowClassLeverage U c) *
      (1 - (rowClassMultiplicity U d : ℝ) * rowClassLeverage U d) /
      (((rowClassMultiplicity U c : ℝ) * rowClassLeverage U c) *
        ((rowClassMultiplicity U d : ℝ) * rowClassLeverage U d)) := by
  have h := rowClass_angle_complement_bound U c d hcd
  simpa only [rowClassAngle, rowClassMass_eq_multiplicity_mul_leverage U hrep] using h

theorem rowClassRep_val_ne {n k : ℕ} (U : Frame n k) (c d : RowClass U)
    (hcd : c ≠ d) : (rowClassRep U c).val ≠ (rowClassRep U d).val := by
  intro h
  have hr : rowClassRep U c = rowClassRep U d := Subtype.ext h
  have he := congrArg (rowClass U) hr
  exact hcd (by simpa only [rowClass_rep] using he)

theorem rowClassRep_gram_sq {n k : ℕ} (U : Frame n k) (c d : RowClass U) :
    gramProjection U (rowClassRep U c).val (rowClassRep U d).val ^ 2 =
      rowClassLeverage U c * rowClassLeverage U d * rowClassAngle U c d := by
  rw [gramProjection_sq_unitRows]
  rfl

/-- Arbitrary scalar functions can be grouped when all raw rows are positive.
The positivity condition is necessary for functions that do not vanish at zero. -/
theorem sum_rowClassMultiplicity_eval_leverage {n k : ℕ} (U : Frame n k)
    (hrep : RowReplacement U) (hpos : ∀ i, 0 < leverage U i) (f : ℝ → ℝ) :
    ∑ c : RowClass U, (rowClassMultiplicity U c : ℝ) * f (rowClassLeverage U c) =
      ∑ i : Fin n, f (leverage U i) := by
  calc
    _ = ∑ c : RowClass U, ∑ i : ActiveRow U with rowClass U i = c, f (leverage U i.val) := by
      apply Finset.sum_congr rfl
      intro c hc
      have hf : ∀ i : ActiveRow U, rowClass U i = c →
          f (leverage U i.val) = f (rowClassLeverage U c) := by
        intro i hi
        congr 1
        exact leverage_eq_of_rowClass_eq U hrep i (rowClassRep U c)
          (hi.trans (rowClass_rep U c).symm)
      rw [Finset.sum_congr rfl (fun i hi => hf i (Finset.mem_filter.mp hi).2)]
      simp [rowClassMultiplicity]
    _ = ∑ i : ActiveRow U, f (leverage U i.val) := Finset.sum_fiberwise _ _ _
    _ = ∑ i : Fin n, f (leverage U i) := by
      apply sum_activeRows U (fun i => f (leverage U i))
      intro i hi
      exact ((ne_of_gt (hpos i)) hi).elim

theorem raw_entropy_eq_actualGrouped {n k : ℕ} (q : ℕ) (U : Frame n k)
    (hrep : RowReplacement U) (hwin : ReciprocalWindow q U) :
    (1 / 2 : ℝ) * ∑ i : Fin n, entropyExcess q (leverage U i) =
      groupedEntropy q (rowClassMultiplicity U) (rowClassLeverage U) := by
  rw [← sum_rowClassMultiplicity_eval_leverage U hrep (reciprocalWindow_pos q U hwin)]
  rfl

theorem actualClass_charge_identity {n k : ℕ} (q : ℕ) (hq : 1 ≤ q) (U : Frame n k)
    (hrep : RowReplacement U) (hwin : ReciprocalWindow q U) :
    (1 / 2 : ℝ) * ∑ i : Fin n, entropyExcess q (leverage U i) =
      (1 / 2 : ℝ) * ∑ c : RowClass U, ∑ d : RowClass U, classWeight U c d *
        (Certificates.sourceCharge q (rowClassMultiplicity U c) (rowClassLeverage U c) +
          Certificates.sourceCharge q (rowClassMultiplicity U d) (rowClassLeverage U d)) := by
  rw [raw_entropy_eq_actualGrouped q U hrep hwin]
  apply grouped_charge_identity q hq _ _ _ (rowClassLeverage_window q U hwin)
  · intro c
    rw [← rowClassMass_eq_multiplicity_mul_leverage U hrep]
    exact rowClassMass_le_one U c
  · exact classWeight_symm U
  · exact classWeight_degree_multiplicity U hrep

end CubeSections
