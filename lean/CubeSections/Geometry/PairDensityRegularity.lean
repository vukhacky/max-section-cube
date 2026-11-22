import CubeSections.Geometry.ReducedFiber
import CubeSections.Geometry.AffineContinuity

/-! Measurability and central continuity of the specified pointwise coarea
representative. No pointwise statement is inferred from an a.e. density class. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace CubeSections

theorem continuous_pairFiberOffset {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : 0 < pairGramDet U i j) : Continuous (pairFiberOffset U i j hdet) :=
  continuous_subtype_val.comp
    ((pairComplementEquiv U i j (ne_of_gt hdet)).symm.toContinuousLinearEquiv.continuous.comp
      (WithLp.prod_continuous_toLp 2 ℝ ℝ))

theorem continuous_reducedOffset {n k : ℕ} (U : Frame n k) (c d : RowClass U) :
    Continuous (reducedOffset U c d) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (remainingRowCount U c d) => ℝ)).comp
  apply continuous_pi
  intro a
  exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ)
    ((remainingRowEquiv U c d).symm a).val.val).comp U.continuous

theorem measurable_pairSliceMass {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : 0 < pairGramDet U i j) (S : Set (E k)) (hS : MeasurableSet S) :
    Measurable (pairSliceMass U i j hdet S) :=
  (measurable_orthogonalFiberMass (pairKernel U i j) S hS).comp
    (((pairComplementEquiv U i j (ne_of_gt hdet)).symm.toContinuousLinearEquiv.continuous.comp
      (WithLp.prod_continuous_toLp 2 ℝ ℝ)).measurable)

theorem measurable_pairPushforwardDensity {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : 0 < pairGramDet U i j) (S : Set (E k)) (hS : MeasurableSet S) :
    Measurable (pairPushforwardDensity U i j hdet S) :=
  measurable_const.mul (measurable_pairSliceMass U i j hdet S hS)

theorem eventually_discardedRowsBound_pairFiberOffset {n k : ℕ} (U : Frame n k)
    (c d : RowClass U) (hcd : c ≠ d) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 0, discardedRowsBound U c d
      (pairFiberOffset U (rowClassRep U c).val (rowClassRep U d).val
        (pairGramDet_classRep_pos U c d hcd) p) := by
  have hc := (continuous_pairFiberOffset U (rowClassRep U c).val (rowClassRep U d).val
    (pairGramDet_classRep_pos U c d hcd)).norm.continuousAt (x := (0 : ℝ × ℝ))
  have he := hc.eventually_lt_const (by simp :
    ‖pairFiberOffset U (rowClassRep U c).val (rowClassRep U d).val
      (pairGramDet_classRep_pos U c d hcd) 0‖ < (1:ℝ)/2)
  filter_upwards [he] with p hp
  intro a ha
  calc
    |(U (pairFiberOffset U _ _ _ p)) a.val| ≤ ‖U (pairFiberOffset U _ _ _ p)‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (U (pairFiberOffset U _ _ _ p)) a.val
    _ = ‖pairFiberOffset U _ _ _ p‖ := U.norm_map _
    _ ≤ (1:ℝ)/2 := hp.le

theorem pairClassSliceMass_eventually_eq_affineMass {n k : ℕ} (U : Frame n k)
    (c d : RowClass U) (hcd : c ≠ d) :
    (pairSliceMass U (rowClassRep U c).val (rowClassRep U d).val
      (pairGramDet_classRep_pos U c d hcd) (U ⁻¹' cube n)) =ᶠ[𝓝 (0 : ℝ × ℝ)]
      (fun p => affineMass (reducedClassFrame U c d hcd)
        (reducedOffset U c d (pairFiberOffset U (rowClassRep U c).val (rowClassRep U d).val
          (pairGramDet_classRep_pos U c d hcd) p))) := by
  filter_upwards [eventually_discardedRowsBound_pairFiberOffset U c d hcd] with p hp
  rw [pairSliceMass_parametrized U _ _ _ _
    ((cube_compact n).isClosed.measurableSet.preimage U.continuous.measurable)]
  have hs := fiber_eq_reduced_or_empty U c d hcd
    (pairFiberOffset U (rowClassRep U c).val (rowClassRep U d).val
      (pairGramDet_classRep_pos U c d hcd) p)
  rw [if_pos hp] at hs
  change volume _ = volume _
  congr 1
  simpa only [Set.mem_preimage, classKernelFrame, add_comm] using hs

theorem continuousAt_pairClassSliceMass_zero {n k : ℕ} (U : Frame n k)
    (c d : RowClass U) (hcd : c ≠ d) :
    ContinuousAt (pairSliceMass U (rowClassRep U c).val (rowClassRep U d).val
      (pairGramDet_classRep_pos U c d hcd) (U ⁻¹' cube n)) 0 := by
  let g := fun p => reducedOffset U c d
    (pairFiberOffset U (rowClassRep U c).val (rowClassRep U d).val
      (pairGramDet_classRep_pos U c d hcd) p)
  have hg : Continuous g := (continuous_reducedOffset U c d).comp (continuous_pairFiberOffset U _ _ _)
  have hg0 : g 0 = 0 := by simp [g]
  have hf : ContinuousAt (affineMass (reducedClassFrame U c d hcd)) (g 0) := by
    rw [hg0]
    exact continuousAt_affineMass_zero _
  exact (hf.comp hg.continuousAt).congr_of_eventuallyEq
    (pairClassSliceMass_eventually_eq_affineMass U c d hcd)

#print axioms measurable_pairPushforwardDensity
#print axioms pairClassSliceMass_eventually_eq_affineMass
#print axioms continuousAt_pairClassSliceMass_zero
end CubeSections
