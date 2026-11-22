import CubeSections.Geometry.PairKernel
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod

/-! Exact disintegration over an orthogonal complement, proved from the
measure-preserving orthogonal decomposition and Tonelli. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubeSections

theorem map_snd_restrict_eq_fiberDensity
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (S : Set (α × β)) (hS : MeasurableSet S) :
    Measure.map Prod.snd ((μ.prod ν).restrict S) =
      ν.withDensity (fun y => μ ((fun x => (x,y)) ⁻¹' S)) := by
  ext s hs
  rw [Measure.map_apply measurable_snd hs,
    Measure.restrict_apply (measurable_snd hs),
    Measure.prod_apply_symm ((measurable_snd hs).inter hS),
    withDensity_apply _ hs, ← lintegral_indicator hs]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ s
  · simp only [Set.indicator_of_mem hy]
    congr 1
    ext x
    simp [hy]
  · simp only [Set.indicator_of_notMem hy]
    have hset : (fun x => (x,y)) ⁻¹' (Prod.snd ⁻¹' s ∩ S) = ∅ := by
      ext x
      simp [hy]
    rw [hset, measure_empty]

def orthogonalCoordinates {k : ℕ} (K : Submodule ℝ (E k)) :
    E k ≃ᵐ K × Kᗮ :=
  K.orthogonalDecomposition.toMeasurableEquiv.trans (MeasurableEquiv.toLp 2 (K × Kᗮ)).symm

theorem orthogonalCoordinates_measurePreserving {k : ℕ} (K : Submodule ℝ (E k)) :
    MeasurePreserving (orthogonalCoordinates K) :=
  (K.orthogonalDecomposition.measurePreserving).trans
    (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod K Kᗮ)

@[simp] theorem orthogonalCoordinates_symm_apply {k : ℕ} (K : Submodule ℝ (E k))
    (z : K × Kᗮ) : (orthogonalCoordinates K).symm z = (z.1 : E k) + (z.2 : E k) := by
  simp [orthogonalCoordinates]

theorem orthogonalCoordinates_snd {k : ℕ} (K : Submodule ℝ (E k)) (x : E k) :
    (orthogonalCoordinates K x).2 = Kᗮ.orthogonalProjectionOnto x := by
  simp [orthogonalCoordinates]

theorem map_restrict_of_measurePreserving_equiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (ν : Measure β) (he : MeasurePreserving e μ ν)
    (S : Set α) :
    Measure.map e (μ.restrict S) = ν.restrict (e.symm ⁻¹' S) := by
  rw [← he.map_eq, e.restrict_map]
  congr 2
  ext x
  simp

def orthogonalFiberMass {k : ℕ} (K : Submodule ℝ (E k)) (S : Set (E k))
    (y : Kᗮ) : ℝ≥0∞ := volume {z : K | (z : E k) + (y : E k) ∈ S}

theorem measurable_orthogonalFiberMass {k : ℕ} (K : Submodule ℝ (E k))
    (S : Set (E k)) (hS : MeasurableSet S) : Measurable (orthogonalFiberMass K S) := by
  exact measurable_measure_prodMk_right
    (hS.preimage (orthogonalCoordinates K).symm.measurable)

theorem orthogonal_projection_map_restrict {k : ℕ} (K : Submodule ℝ (E k))
    (S : Set (E k)) (hS : MeasurableSet S) :
    Measure.map Kᗮ.orthogonalProjectionOnto (volume.restrict S) =
      volume.withDensity (orthogonalFiberMass K S) := by
  have hm := map_restrict_of_measurePreserving_equiv (orthogonalCoordinates K)
    volume volume (orthogonalCoordinates_measurePreserving K) S
  have hcomp : (Prod.snd ∘ orthogonalCoordinates K) = Kᗮ.orthogonalProjectionOnto := by
    funext x
    exact orthogonalCoordinates_snd K x
  calc
    _ = Measure.map Prod.snd (Measure.map (orthogonalCoordinates K) (volume.restrict S)) := by
      rw [Measure.map_map measurable_snd (orthogonalCoordinates K).measurable, hcomp]
    _ = Measure.map Prod.snd (volume.restrict ((orthogonalCoordinates K).symm ⁻¹' S)) := by rw [hm]
    _ = volume.withDensity (fun y : Kᗮ => volume
        ((fun z : K => (z,y)) ⁻¹' ((orthogonalCoordinates K).symm ⁻¹' S))) :=
      map_snd_restrict_eq_fiberDensity volume volume _
        (hS.preimage (orthogonalCoordinates K).symm.measurable)
    _ = _ := by
      congr 1

end CubeSections
