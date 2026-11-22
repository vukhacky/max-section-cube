import CubeSections.Geometry.OrthogonalFibers
import Mathlib.Analysis.Normed.Module.Span
import Mathlib.Analysis.Normed.Group.Bounded

/-! A bounded measurable body has a uniformly bounded one-dimensional marginal
in every unit direction. The bound is finite; no sharp constant is needed for
Gaussian-quantile integrability. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal InnerProductSpace
namespace CubeSections

theorem bounded_orthogonalProjection_measure_le {k : ℕ} (L : Submodule ℝ (E k))
    (S : Set (E k)) (hS : Bornology.IsBounded S) :
    ∃ C : ℝ≥0, Measure.map L.orthogonalProjectionOnto (volume.restrict S) ≤
      (C : ℝ≥0∞) • volume := by
  obtain ⟨R, hRpos, hR⟩ := hS.exists_pos_norm_le
  let B : Set Lᗮ := Metric.closedBall 0 R
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hBfin : volume B ≠ ∞ := (isCompact_closedBall (0 : Lᗮ) R).measure_ne_top
  refine ⟨(volume B).toNNReal, ?_⟩
  apply Measure.le_iff.mpr
  intro T hT
  rw [Measure.map_apply L.orthogonalProjectionOnto.continuous.measurable hT,
    Measure.restrict_apply (L.orthogonalProjectionOnto.continuous.measurable hT),
    smul_apply, smul_eq_mul, ENNReal.coe_toNNReal hBfin]
  calc
    volume (L.orthogonalProjectionOnto ⁻¹' T ∩ S) ≤
        volume ((orthogonalCoordinates L) ⁻¹' (T ×ˢ B)) := by
      apply measure_mono
      rintro x ⟨hxT,hxS⟩
      constructor
      · simpa [orthogonalCoordinates] using hxT
      · rw [orthogonalCoordinates_snd]
        change dist (Lᗮ.orthogonalProjectionOnto x) 0 ≤ R
        rw [dist_zero_right]
        exact (Lᗮ.norm_orthogonalProjectionOnto_apply_le x).trans (hR x hxS)
    _ = volume (T ×ˢ B) :=
      (orthogonalCoordinates_measurePreserving L).measure_preimage (hT.prod hB).nullMeasurableSet
    _ = volume B * volume T := by
      change ((volume : Measure L).prod (volume : Measure Lᗮ)) (T ×ˢ B) = _
      rw [Measure.prod_prod, mul_comm]

theorem bounded_unit_marginal_measure_le {k : ℕ} (S : Set (E k))
    (hS : Bornology.IsBounded S) (u : E k) (hu : ‖u‖ = 1) :
    ∃ C : ℝ≥0, Measure.map (fun x : E k => inner ℝ u x) (volume.restrict S) ≤
      (C : ℝ≥0∞) • volume := by
  let L : Submodule ℝ (E k) := ℝ ∙ u
  let e : ℝ ≃ₗᵢ[ℝ] L := LinearIsometryEquiv.toSpanUnitSingleton u hu
  obtain ⟨C, hC⟩ := bounded_orthogonalProjection_measure_le L S hS
  refine ⟨C, ?_⟩
  have he : Measurable (e.symm : L → ℝ) := e.symm.continuous.measurable
  have hcomp : (e.symm ∘ L.orthogonalProjectionOnto) = (fun x : E k => inner ℝ u x) := by
    funext x
    apply e.injective
    rw [Function.comp_apply, e.apply_symm_apply]
    apply Subtype.ext
    change L.starProjection x = (inner ℝ u x) • u
    exact Submodule.starProjection_unit_singleton ℝ hu x
  have h := Measure.map_mono hC he
  rw [Measure.map_map he L.orthogonalProjectionOnto.continuous.measurable,
    hcomp, Measure.map_smul _ he.aemeasurable, e.symm.measurePreserving.map_eq] at h
  exact h

theorem bounded_unit_marginal_restrict_measure_le {k : ℕ} (S : Set (E k))
    (hS : Bornology.IsBounded S) (u : E k) (hu : ‖u‖ = 1) (r : ℝ)
    (hsupport : S ⊆ (fun x : E k => inner ℝ u x) ⁻¹' Ioo (-r) r) :
    ∃ C : ℝ≥0, Measure.map (fun x : E k => inner ℝ u x) (volume.restrict S) ≤
      (C : ℝ≥0∞) • volume.restrict (Ioo (-r) r) := by
  obtain ⟨C,hC⟩ := bounded_unit_marginal_measure_le S hS u hu
  refine ⟨C, ?_⟩
  have hF : Measurable (fun x : E k => inner ℝ u x) := (continuous_const.inner continuous_id).measurable
  have heq : (Measure.map (fun x : E k => inner ℝ u x) (volume.restrict S)).restrict (Ioo (-r) r) =
      Measure.map (fun x : E k => inner ℝ u x) (volume.restrict S) := by
    ext T hT
    rw [Measure.restrict_apply hT, Measure.map_apply hF (hT.inter measurableSet_Ioo),
      Measure.map_apply hF hT, Measure.restrict_apply (hF (hT.inter measurableSet_Ioo)),
      Measure.restrict_apply (hF hT)]
    congr 1
    ext x
    constructor
    · rintro ⟨⟨hxT,hxI⟩,hxS⟩
      exact ⟨hxT,hxS⟩
    · rintro ⟨hxT,hxS⟩
      exact ⟨⟨hxT,hsupport hxS⟩,hxS⟩
  have h := Measure.restrict_mono_measure hC (Ioo (-r) r)
  rw [heq, Measure.restrict_smul] at h
  exact h

#print axioms bounded_orthogonalProjection_measure_le
#print axioms bounded_unit_marginal_measure_le
#print axioms bounded_unit_marginal_restrict_measure_le
end CubeSections
