import CubeSections.Geometry.ComplementFrame
import CubeSections.Geometry.LinearDensity
import CubeSections.Geometry.AffineContinuity
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# The actual complementary projection density of the cube

The density is the specified affine-section volume, not an arbitrary a.e.
Radon--Nikodym representative. Orthogonal decomposition proves the pushforward
identity; continuity at the origin follows from the actual affine-volume theorem.
No Brunn--Minkowski inequality is used.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubeSections

theorem measurable_affineMass {n k : ℕ} (U : Frame n k) : Measurable (affineMass U) := by
  have hs : MeasurableSet {p : E k × E n | p.2 + U p.1 ∈ cube n} :=
    (cube_compact n).isClosed.measurableSet.preimage
      (continuous_snd.add (U.continuous.comp continuous_fst)).measurable
  exact measurable_measure_prodMk_right hs

theorem measurable_affineVolume {n k : ℕ} (U : Frame n k) : Measurable (affineVolume U) :=
  (measurable_affineMass U).ennreal_toReal

theorem orthogonalFiberMass_range_cube {n k : ℕ} (U : Frame n k)
    (y : U.toLinearMap.rangeᗮ) :
    orthogonalFiberMass U.toLinearMap.range (cube n) y = affineMass U y := by
  have hs : MeasurableSet {z : U.toLinearMap.range | (z : E n) + (y : E n) ∈ cube n} :=
    (cube_compact n).isClosed.measurableSet.preimage
      (continuous_subtypeVal.add continuous_const).measurable
  have hm := U.equivRange.measurePreserving.measure_preimage hs.nullMeasurableSet
  simpa only [orthogonalFiberMass, affineMass, affineSlab, Set.preimage_ofPred_eq,
    LinearIsometry.equivRange_apply_coe, add_comm] using hm.symm

/-- Exact projection law with the actual intrinsic affine-section mass. -/
theorem complementaryFrame_map_cube {n k : ℕ} (U : Frame n k) :
    Measure.map (frameAdjoint (complementaryFrame U)) (volume.restrict (cube n)) =
      volume.withDensity (fun y : E (n-k) => affineMass U (complementaryFrame U y)) := by
  let e := (frameComplementBasis U).repr.toMeasurableEquiv
  let ρ : frameComplement U → ℝ≥0∞ :=
    fun y => orthogonalFiberMass U.toLinearMap.range (cube n) y
  have he : MeasurePreserving e := (frameComplementBasis U).repr.measurePreserving
  have hcomp : (e ∘ (frameComplement U).orthogonalProjectionOnto) =
      frameAdjoint (complementaryFrame U) := by
    funext x
    exact (frameAdjoint_complementaryFrame U x).symm
  calc
    _ = Measure.map e (Measure.map (frameComplement U).orthogonalProjectionOnto
        (volume.restrict (cube n))) := by
      rw [Measure.map_map e.measurable
        (frameComplement U).orthogonalProjectionOnto.continuous.measurable, hcomp]
    _ = Measure.map e (volume.withDensity ρ) := by
      exact congrArg (Measure.map e) (orthogonal_projection_map_restrict U.toLinearMap.range
        (cube n) (cube_compact n).isClosed.measurableSet)
    _ = _ := by
      rw [map_withDensity_equiv, he.map_eq]
      congr 1
      funext y
      exact orthogonalFiberMass_range_cube U (e.symm y)

/-- Real density used by Fourier inversion. -/
def complementDensity {n k : ℕ} (U : Frame n k) (y : E (n-k)) : ℝ :=
  affineVolume U (complementaryFrame U y)

theorem complementDensity_nonneg {n k : ℕ} (U : Frame n k) (y : E (n-k)) :
    0 ≤ complementDensity U y := affineVolume_nonneg U _

theorem measurable_complementDensity {n k : ℕ} (U : Frame n k) : Measurable (complementDensity U) :=
  (measurable_affineVolume U).comp (complementaryFrame U).continuous.measurable

theorem ofReal_complementDensity {n k : ℕ} (U : Frame n k) (y : E (n-k)) :
    ENNReal.ofReal (complementDensity U y) = affineMass U (complementaryFrame U y) :=
  ENNReal.ofReal_toReal (affineMass_ne_top U _)

theorem complementaryFrame_map_cube_real_density {n k : ℕ} (U : Frame n k) :
    Measure.map (frameAdjoint (complementaryFrame U)) (volume.restrict (cube n)) =
      volume.withDensity (fun y => ENNReal.ofReal (complementDensity U y)) := by
  simp_rw [ofReal_complementDensity]
  exact complementaryFrame_map_cube U

theorem lintegral_complementDensity {n k : ℕ} (U : Frame n k) :
    (∫⁻ y, ENNReal.ofReal (complementDensity U y)) = volume (cube n) := by
  have h := congrArg (fun μ : Measure (E (n-k)) => μ Set.univ)
    (complementaryFrame_map_cube_real_density U)
  rw [Measure.map_apply (frameAdjoint (complementaryFrame U)).continuous.measurable
    MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h
  exact h.symm

theorem integrable_complementDensity {n k : ℕ} (U : Frame n k) : Integrable (complementDensity U) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_complementDensity U).aestronglyMeasurable
    (ae_of_all _ (complementDensity_nonneg U))).1
  rw [lintegral_complementDensity]
  exact (cube_compact n).measure_ne_top

theorem continuousAt_complementDensity_zero {n k : ℕ} (U : Frame n k) :
    ContinuousAt (complementDensity U) 0 := by
  exact (continuousAt_affineVolume_zero U).comp_of_eq
    ((complementaryFrame U).continuous.continuousAt (x := (0 : E (n-k))))
    (map_zero (complementaryFrame U))

@[simp] theorem complementDensity_zero {n k : ℕ} (U : Frame n k) :
    complementDensity U 0 = sectionVolume U := by
  simp only [complementDensity, map_zero, affineVolume_zero]

#print axioms complementaryFrame_map_cube
#print axioms complementaryFrame_map_cube_real_density
#print axioms integrable_complementDensity
#print axioms continuousAt_complementDensity_zero
#print axioms complementDensity_zero
end CubeSections
