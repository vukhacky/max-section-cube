import CubeSections.Geometry.PairJacobian
import CubeSections.Geometry.ReducedFrame

/-! Exact two-coordinate coarea for the actual cube section. The density is a
specific fiber-volume representative divided by 4*sqrt(cd-P^2), not an assumed
Radon--Nikodym representative. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubeSections

def pairFiberOffset {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : 0 < pairGramDet U i j) (p : ℝ × ℝ) : E k :=
  ((pairComplementEquiv U i j (ne_of_gt hdet)).symm (WithLp.toLp 2 p) : E k)

def pairSliceMass {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : 0 < pairGramDet U i j) (S : Set (E k)) (p : ℝ × ℝ) : ℝ≥0∞ :=
  orthogonalFiberMass (pairKernel U i j) S
    ((pairComplementEquiv U i j (ne_of_gt hdet)).symm (WithLp.toLp 2 p))

def pairPushforwardDensity {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : 0 < pairGramDet U i j) (S : Set (E k)) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (4 * Real.sqrt (pairGramDet U i j))⁻¹ * pairSliceMass U i j hdet S p

theorem pairEuclideanMap_coarea {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : 0 < pairGramDet U i j) (S : Set (E k)) (hS : MeasurableSet S) :
    Measure.map (pairEuclideanMap U i j) (volume.restrict S) =
      volume.withDensity (fun p : PairPlane =>
        ENNReal.ofReal (4 * Real.sqrt (pairGramDet U i j))⁻¹ *
          orthogonalFiberMass (pairKernel U i j) S
            ((pairComplementEquiv U i j (ne_of_gt hdet)).symm p)) := by
  let e := pairComplementEquiv U i j (ne_of_gt hdet)
  have he : Measurable (e : (pairKernel U i j)ᗮ → PairPlane) :=
    e.toContinuousLinearEquiv.continuous.measurable
  have hcomp : (e ∘ (pairKernel U i j)ᗮ.orthogonalProjectionOnto) = pairEuclideanMap U i j := by
    funext x
    exact pairComplementEquiv_projection U i j (ne_of_gt hdet) x
  calc
    _ = Measure.map e (Measure.map (pairKernel U i j)ᗮ.orthogonalProjectionOnto (volume.restrict S)) := by
      rw [Measure.map_map he (pairKernel U i j)ᗮ.orthogonalProjectionOnto.continuous.measurable, hcomp]
    _ = Measure.map e (volume.withDensity (orthogonalFiberMass (pairKernel U i j) S)) := by
      rw [orthogonal_projection_map_restrict _ _ hS]
    _ = _ := by
      rw [linearEquiv_map_withDensity]
      simp only [e, pairComplementEquiv_normDet U i j hdet]

theorem pairCoordinateMap_coarea {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : 0 < pairGramDet U i j) (S : Set (E k)) (hS : MeasurableSet S) :
    Measure.map (pairCoordinateMap U i j) (volume.restrict S) =
      volume.withDensity (pairPushforwardDensity U i j hdet S) := by
  let e := (MeasurableEquiv.toLp 2 (ℝ × ℝ)).symm
  have he : MeasurePreserving e := WithLp.volume_preserving_symm_measurableEquiv_toLp_prod ℝ ℝ
  have hcomp : (e ∘ pairEuclideanMap U i j) = pairCoordinateMap U i j := rfl
  calc
    _ = Measure.map e (Measure.map (pairEuclideanMap U i j) (volume.restrict S)) := by
      rw [Measure.map_map e.measurable (pairEuclideanMap U i j).continuous_of_finiteDimensional.measurable,
        hcomp]
    _ = Measure.map e (volume.withDensity (fun p : PairPlane =>
        ENNReal.ofReal (4 * Real.sqrt (pairGramDet U i j))⁻¹ *
          orthogonalFiberMass (pairKernel U i j) S
            ((pairComplementEquiv U i j (ne_of_gt hdet)).symm p))) := by
      rw [pairEuclideanMap_coarea U i j hdet S hS]
    _ = _ := by
      rw [map_withDensity_equiv, he.map_eq]
      rfl

theorem pairSection_coarea {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : 0 < pairGramDet U i j) :
    Measure.map (normalizedPairCoordinates U i j) (volume.restrict (U ⁻¹' cube n)) =
      volume.withDensity (pairPushforwardDensity U i j hdet (U ⁻¹' cube n)) :=
  pairCoordinateMap_coarea U i j hdet _
    ((cube_compact n).isClosed.measurableSet.preimage U.continuous.measurable)

theorem pairFiberOffset_coordinates {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : 0 < pairGramDet U i j) (p : ℝ × ℝ) :
    pairCoordinateMap U i j (pairFiberOffset U i j hdet p) = p := by
  have h := congrArg WithLp.ofLp
    ((pairComplementEquiv U i j (ne_of_gt hdet)).apply_symm_apply (WithLp.toLp 2 p))
  exact h

theorem pairSliceMass_parametrized {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : 0 < pairGramDet U i j) (S : Set (E k)) (hS : MeasurableSet S)
    (p : ℝ × ℝ) :
    pairSliceMass U i j hdet S p =
      volume {x : E (k - 2) | pairKernelFrame U i j (ne_of_gt hdet) x +
        pairFiberOffset U i j hdet p ∈ S} := by
  let b := pairKernelBasis U i j (ne_of_gt hdet)
  let y := (pairComplementEquiv U i j (ne_of_gt hdet)).symm (WithLp.toLp 2 p)
  have hs : MeasurableSet {z : pairKernel U i j | (z : E k) + (y : E k) ∈ S} :=
    hS.preimage (continuous_subtype_val.add continuous_const).measurable
  have hm := b.repr.symm.measurePreserving.measure_preimage hs.nullMeasurableSet
  exact hm.symm

theorem pairClassSliceMass_le_affineMass {n k : ℕ} (U : Frame n k)
    (c d : RowClass U) (hcd : c ≠ d) (p : ℝ × ℝ) :
    pairSliceMass U (rowClassRep U c).val (rowClassRep U d).val
      (pairGramDet_classRep_pos U c d hcd) (U ⁻¹' cube n) p ≤
      affineMass (reducedClassFrame U c d hcd)
        (reducedOffset U c d (pairFiberOffset U (rowClassRep U c).val (rowClassRep U d).val
          (pairGramDet_classRep_pos U c d hcd) p)) := by
  rw [pairSliceMass_parametrized U _ _ _ _
    ((cube_compact n).isClosed.measurableSet.preimage U.continuous.measurable)]
  apply measure_mono
  intro x hx
  apply fiber_subset_reduced_affineSlab U c d hcd _
  simpa only [Set.mem_setOf_eq, Set.mem_preimage, classKernelFrame, add_comm] using hx

end CubeSections
