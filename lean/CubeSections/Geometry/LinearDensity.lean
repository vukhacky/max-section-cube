import CubeSections.Geometry.NormalizationFrame
import CubeSections.Geometry.OrthogonalFibers
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Linear changes of variables for actual fiber densities. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubeSections

theorem map_withDensity_equiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (ρ : α → ℝ≥0∞) :
    Measure.map e (μ.withDensity ρ) =
      (Measure.map e μ).withDensity (ρ ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_map_equiv, ← lintegral_indicator (e.measurable hs)]
  apply lintegral_congr
  intro x
  by_cases hx : e x ∈ s <;> simp [hx]

section Euclidean
variable {V W : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
variable [MeasurableSpace W] [BorelSpace W]

theorem linearEquiv_volume_image (e : V ≃ₗ[ℝ] W) (S : Set V) :
    volume (e '' S) = ENNReal.ofReal e.toLinearMap.normDet * volume S := by
  have h := e.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume S
  rw [e.finrank_eq, InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h
  exact h

theorem linearEquiv_map_volume (e : V ≃ₗ[ℝ] W) :
    Measure.map e volume = ENNReal.ofReal e.symm.toLinearMap.normDet • volume := by
  ext s hs
  have he : Measurable (e : V → W) := e.toContinuousLinearEquiv.continuous.measurable
  rw [Measure.map_apply he hs,
    Measure.smul_apply, smul_eq_mul]
  have hset : e ⁻¹' s = e.symm '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [hset]
  exact linearEquiv_volume_image e.symm s

theorem linearEquiv_normDet_symm (e : V ≃ₗ[ℝ] W) :
    e.symm.toLinearMap.normDet = e.toLinearMap.normDet⁻¹ := by
  have h := LinearMap.normDet_comp_of_finrank_eq e.toLinearMap e.symm.toLinearMap e.finrank_eq
  have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext x; simp
  rw [he, LinearMap.normDet_id] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem linearEquiv_map_withDensity (e : V ≃ₗ[ℝ] W)
    (ρ : V → ℝ≥0∞) :
    Measure.map e (volume.withDensity ρ) =
      volume.withDensity (fun y => ENNReal.ofReal e.toLinearMap.normDet⁻¹ * ρ (e.symm y)) := by
  let em := e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hm := map_withDensity_equiv em volume ρ
  change Measure.map e (volume.withDensity ρ) =
    (Measure.map e volume).withDensity (ρ ∘ e.symm) at hm
  rw [hm, linearEquiv_map_volume, linearEquiv_normDet_symm,
    withDensity_smul_measure]
  calc
    _ = volume.withDensity ((ENNReal.ofReal e.toLinearMap.normDet⁻¹) • (ρ ∘ e.symm)) :=
      (withDensity_smul' (μ := (volume : Measure W))
        (ENNReal.ofReal e.toLinearMap.normDet⁻¹) (ρ ∘ e.symm) ENNReal.ofReal_ne_top).symm
    _ = _ := by
      congr 1
end Euclidean

end CubeSections
