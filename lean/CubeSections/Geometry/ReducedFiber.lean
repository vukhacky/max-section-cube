import CubeSections.Geometry.PairCoarea

/-! Exact fiber identification, including the constraints from the removed
classes and the exact central fiber. -/
noncomputable section
open Set MeasureTheory Classical
open scoped ENNReal
namespace CubeSections

def discardedRowsBound {n k : ℕ} (U : Frame n k) (c d : RowClass U) (z : E k) : Prop :=
  ∀ a : ActiveRow U, rowClass U a = c ∨ rowClass U a = d → |(U z) a.val| ≤ (1:ℝ)/2

theorem fiber_mem_iff_reduced {n k : ℕ} (U : Frame n k) (c d : RowClass U)
    (hcd : c ≠ d) (z : E k) (x : E (k-2)) :
    U (z + classKernelFrame U c d hcd x) ∈ cube n ↔
      discardedRowsBound U c d z ∧
        x ∈ affineSlab (reducedClassFrame U c d hcd) (reducedOffset U c d z) := by
  constructor
  · intro hx
    refine ⟨?_, fiber_subset_reduced_affineSlab U c d hcd z hx⟩
    intro a ha
    have h := hx a.val
    simpa only [map_add, PiLp.add_apply, classKernelFrame_class_zero U c d hcd a ha,
      add_zero] using h
  · rintro ⟨hdiscard,hred⟩ i
    by_cases hi : 0 < leverage U i
    · let a : ActiveRow U := ⟨i,hi⟩
      by_cases ha : rowClass U a = c ∨ rowClass U a = d
      · have hz := classKernelFrame_class_zero U c d hcd a ha x
        have h := hdiscard a ha
        change (U (classKernelFrame U c d hcd x)) i = 0 at hz
        change |(U z) i| ≤ (1:ℝ)/2 at h
        simpa only [map_add, PiLp.add_apply, hz, add_zero] using h
      · have hkeep : rowClass U a ≠ c ∧ rowClass U a ≠ d := by tauto
        let b : RemainingRow U c d := ⟨a,hkeep⟩
        have h := hred (remainingRowEquiv U c d b)
        change |reducedOffset U c d z (remainingRowEquiv U c d b) +
          reducedClassFrame U c d hcd x (remainingRowEquiv U c d b)| ≤ (1:ℝ)/2 at h
        simp only [reducedClassFrame_apply, reducedOffset, WithLp.ofLp_toLp,
          Equiv.symm_apply_apply] at h
        simpa only [map_add, PiLp.add_apply] using h
    · have hz : leverage U i = 0 := le_antisymm (le_of_not_gt hi) (leverage_nonneg U i)
      rw [(leverage_eq_zero_iff_coordinate_zero U i).mp hz]
      norm_num

theorem fiber_eq_reduced_or_empty {n k : ℕ} (U : Frame n k) (c d : RowClass U)
    (hcd : c ≠ d) (z : E k) :
    {x : E (k-2) | U (z + classKernelFrame U c d hcd x) ∈ cube n} =
      if discardedRowsBound U c d z then
        affineSlab (reducedClassFrame U c d hcd) (reducedOffset U c d z) else ∅ := by
  ext x
  rw [Set.mem_setOf_eq, fiber_mem_iff_reduced]
  split_ifs <;> simp_all

@[simp] theorem discardedRowsBound_zero {n k : ℕ} (U : Frame n k) (c d : RowClass U) :
    discardedRowsBound U c d 0 := by
  intro a ha
  simp

@[simp] theorem reducedOffset_zero {n k : ℕ} (U : Frame n k) (c d : RowClass U) :
    reducedOffset U c d 0 = 0 := by ext a; simp [reducedOffset]

theorem central_classKernel_slab {n k : ℕ} (U : Frame n k) (c d : RowClass U)
    (hcd : c ≠ d) :
    {x : E (k-2) | U (classKernelFrame U c d hcd x) ∈ cube n} =
      reducedClassFrame U c d hcd ⁻¹' cube (remainingRowCount U c d) := by
  simpa only [zero_add, discardedRowsBound_zero, ↓reduceIte, reducedOffset_zero, affineSlab_zero]
    using fiber_eq_reduced_or_empty U c d hcd 0

@[simp] theorem pairFiberOffset_zero {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : 0 < pairGramDet U i j) : pairFiberOffset U i j hdet 0 = 0 := by
  simp [pairFiberOffset]

theorem pairClassSliceMass_zero {n k : ℕ} (U : Frame n k) (c d : RowClass U)
    (hcd : c ≠ d) :
    pairSliceMass U (rowClassRep U c).val (rowClassRep U d).val
      (pairGramDet_classRep_pos U c d hcd) (U ⁻¹' cube n) 0 =
      sectionMass (reducedClassFrame U c d hcd) := by
  rw [pairSliceMass_parametrized U _ _ _ _
    ((cube_compact n).isClosed.measurableSet.preimage U.continuous.measurable), pairFiberOffset_zero]
  simp only [add_zero, Set.mem_preimage]
  change volume {x : E (k-2) | U (classKernelFrame U c d hcd x) ∈ cube n} = _
  rw [central_classKernel_slab]
  rfl

#print axioms fiber_mem_iff_reduced
#print axioms fiber_eq_reduced_or_empty
#print axioms pairClassSliceMass_zero
end CubeSections
