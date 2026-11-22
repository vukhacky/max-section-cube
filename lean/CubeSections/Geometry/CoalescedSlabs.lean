import CubeSections.Geometry.CoalescedFrame
import CubeSections.Analysis.SlabVolumeBound

/-! Coalescence preserves the actual slab body and entropy factor. Zero rows of
the original frame contribute no constraint and no logarithmic charge. -/

noncomputable section
open Set Classical
open scoped BigOperators InnerProductSpace

namespace CubeSections

def coalescedCubeRadius {n k : ℕ} (U : Frame n k) (j : Fin (rowClassCount U)) : ℝ :=
  (2 * Real.sqrt (rowClassLeverage U ((rowClassEquiv U).symm j)))⁻¹

theorem coalescedCubeRadius_pos {n k : ℕ} (U : Frame n k) (j : Fin (rowClassCount U)) :
    0 < coalescedCubeRadius U j := by
  have hp := rowClassLeverage_pos U ((rowClassEquiv U).symm j)
  unfold coalescedCubeRadius
  positivity

theorem normalizedFrameCoordinate_coalesced {n k : ℕ} (U : Frame n k)
    (j : Fin (rowClassCount U)) (x : E k) :
    normalizedFrameCoordinate (coalescedFrame U) j x =
      inner ℝ (rowClassUnit U ((rowClassEquiv U).symm j)) x := by
  rw [normalizedFrameCoordinate_eq, coalescedFrame_apply, leverage_coalescedFrame]
  exact mul_div_cancel_left₀ _ (ne_of_gt (Real.sqrt_pos.mpr (rowClassMass_pos U _)))

theorem abs_coordinate_eq_of_rowClass_eq {n k : ℕ} (U : Frame n k)
    (hrep : RowReplacement U) (i j : ActiveRow U) (h : rowClass U i = rowClass U j)
    (x : E k) : |(U x) i.val| = |(U x) j.val| := by
  rw [unitRow_coordinate U i, unitRow_coordinate U j,
    leverage_eq_of_rowClass_eq U hrep i j h]
  rcases (rowClass_eq_iff U i j).1 h with hunit | hunit
  · rw [hunit]
  · rw [hunit, inner_neg_left, mul_neg, abs_neg]

theorem coalescedCubeRadius_constraint {n k : ℕ} (U : Frame n k)
    (j : Fin (rowClassCount U)) (x : E k) :
    normalizedFrameCoordinate (coalescedFrame U) j x ∈
      Ioo (-coalescedCubeRadius U j) (coalescedCubeRadius U j) ↔
      |(U x) (rowClassRep U ((rowClassEquiv U).symm j)).val| < (1 : ℝ) / 2 := by
  let c := (rowClassEquiv U).symm j
  have hs : 0 < Real.sqrt (rowClassLeverage U c) := Real.sqrt_pos.mpr (rowClassLeverage_pos U c)
  have hr : coalescedCubeRadius U j = ((1 : ℝ) / 2) / Real.sqrt (rowClassLeverage U c) := by
    unfold coalescedCubeRadius c
    field_simp
  rw [mem_Ioo, ← abs_lt, normalizedFrameCoordinate_coalesced, hr, lt_div_iff₀ hs,
    unitRow_coordinate U (rowClassRep U c), abs_mul]
  change |inner ℝ (rowClassUnit U c) x| * Real.sqrt (rowClassLeverage U c) < 1 / 2 ↔
    |Real.sqrt (rowClassLeverage U c)| * |inner ℝ (rowClassUnit U c) x| < 1 / 2
  rw [abs_of_pos hs, mul_comm]

theorem coalescedSlab_eq_openSection {n k : ℕ} (U : Frame n k) (hrep : RowReplacement U) :
    frameSlabInterior (coalescedFrame U) (coalescedCubeRadius U) =
      {x : E k | ∀ i, |(U x) i| < (1 : ℝ) / 2} := by
  ext x
  constructor
  · intro hx i
    by_cases hi : 0 < leverage U i
    · let a : ActiveRow U := ⟨i, hi⟩
      have hc := (coalescedCubeRadius_constraint U (rowClassEquiv U (rowClass U a)) x).1
        (hx (rowClassEquiv U (rowClass U a)))
      simp only [Equiv.symm_apply_apply] at hc
      have heq := abs_coordinate_eq_of_rowClass_eq U hrep a (rowClassRep U (rowClass U a))
        (rowClass_rep U _).symm x
      exact heq.trans_lt hc
    · have hz : leverage U i = 0 := le_antisymm (le_of_not_gt hi) (leverage_nonneg U i)
      rw [(leverage_eq_zero_iff_coordinate_zero U i).1 hz x]
      norm_num
  · intro hx j
    exact (coalescedCubeRadius_constraint U j x).2 (hx _)

theorem coalescedSlabVolume {n k : ℕ} (U : Frame n k) (hrep : RowReplacement U) :
    frameSlabVolume (coalescedFrame U) (coalescedCubeRadius U) = sectionVolume U := by
  rw [frameSlabVolume, coalescedSlab_eq_openSection U hrep, frame_openSlab_volume]

theorem sum_rowClassMass_eval {n k : ℕ} (U : Frame n k) (hrep : RowReplacement U)
    (f : ℝ → ℝ) :
    (∑ c : RowClass U, rowClassMass U c * f (rowClassLeverage U c)) =
      ∑ i : Fin n, leverage U i * f (leverage U i) := by
  calc
    _ = ∑ c : RowClass U, ∑ i : ActiveRow U with rowClass U i = c,
        leverage U i.val * f (leverage U i.val) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [rowClassMass, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hl := leverage_eq_of_rowClass_eq U hrep i (rowClassRep U c)
        ((Finset.mem_filter.mp hi).2.trans (rowClass_rep U c).symm)
      change leverage U i.val * f (rowClassLeverage U c) = _
      rw [hl]
      rfl
    _ = ∑ i : ActiveRow U, leverage U i.val * f (leverage U i.val) :=
      Finset.sum_fiberwise _ _ _
    _ = ∑ i : Fin n, leverage U i * f (leverage U i) :=
      sum_activeRows U (fun i => leverage U i * f (leverage U i)) (fun i hi => by simp [hi])

theorem coalescedSlabLogFactor {n k : ℕ} (U : Frame n k) (hrep : RowReplacement U) :
    frameSlabLogFactor (coalescedFrame U) (coalescedCubeRadius U) = slabLogBound U := by
  have hl (j : Fin (rowClassCount U)) :
      Real.log (2 * coalescedCubeRadius U j) =
        -Real.log (rowClassLeverage U ((rowClassEquiv U).symm j)) / 2 := by
    have hp := rowClassLeverage_pos U ((rowClassEquiv U).symm j)
    have hr : 2 * coalescedCubeRadius U j =
        (Real.sqrt (rowClassLeverage U ((rowClassEquiv U).symm j)))⁻¹ := by
      unfold coalescedCubeRadius
      field_simp
    rw [hr, Real.log_inv, Real.log_sqrt hp.le]
    ring
  unfold frameSlabLogFactor
  simp_rw [leverage_coalescedFrame, hl]
  rw [(rowClassEquiv U).symm.sum_comp
    (fun c => rowClassMass U c * (-Real.log (rowClassLeverage U c) / 2))]
  rw [sum_rowClassMass_eval U hrep (fun t => -Real.log t / 2)]
  unfold slabLogBound
  simp_rw [← mul_div_assoc, mul_neg]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

theorem coalescedSlabDeficit {n k : ℕ} (U : Frame n k) (hrep : RowReplacement U) :
    frameSlabLogFactor (coalescedFrame U) (coalescedCubeRadius U) -
      Real.log (frameSlabVolume (coalescedFrame U) (coalescedCubeRadius U)) = slabDeficit U := by
  rw [coalescedSlabLogFactor U hrep, coalescedSlabVolume U hrep]
  rfl

end CubeSections
