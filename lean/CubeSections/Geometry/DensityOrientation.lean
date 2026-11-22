import CubeSections.Geometry.LinearDensity
import CubeSections.Certificates.ActualGroupedComparison

/-! Density caps pass through the cube-preserving coordinate reflection.
This transports the measure directly and avoids changing the quotient type of
row classes or their original multiplicities. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubeSections.Certificates

def planarFirstReflection : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ) (MeasurableEquiv.refl ℝ)

theorem planarFirstReflection_measurePreserving : MeasurePreserving planarFirstReflection := by
  change MeasurePreserving (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ))
    ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume)
  exact (Measure.measurePreserving_neg volume).prod ⟨measurable_id, Measure.map_id⟩

theorem sourcePairDensity_flipRowFrame {n k : ℕ} (U : Frame n k)
    (p : Parameters) (i j : Fin n) (hij : i ≠ j) (c d s : ℝ)
    (h : SourcePairDensity U p i j c d s) :
    SourcePairDensity (flipRowFrame U i) p i j c d s := by
  obtain ⟨ρ,hmap,hcap⟩ := h
  let e := planarFirstReflection
  have he : MeasurePreserving e := planarFirstReflection_measurePreserving
  have hF : normalizedPairCoordinates (flipRowFrame U i) i j = e ∘ normalizedPairCoordinates U i j := by
    funext x
    ext <;> simp [normalizedPairCoordinates, e, planarFirstReflection, hij.symm, mul_neg] <;> rfl
  refine ⟨ρ ∘ e.symm, ?_, ?_⟩
  · rw [flipRowFrame_preimage_cube, hF,
      ← Measure.map_map e.measurable (measurable_normalizedPairCoordinates U i j),
      hmap, map_withDensity_equiv, he.map_eq]
  · have hc := he.symm.quasiMeasurePreserving.ae hcap
    simpa only [Function.comp_def, flipRowFrame_volume] using hc

theorem sourcePairDensity_orientedPairFrame {n k : ℕ} (U : Frame n k)
    (p : Parameters) (i j : Fin n) (hij : i ≠ j) (c d s : ℝ)
    (h : SourcePairDensity U p i j c d s) :
    SourcePairDensity (orientedPairFrame U i j) p i j c d s := by
  unfold orientedPairFrame
  split_ifs
  · exact h
  · exact sourcePairDensity_flipRowFrame U p i j hij c d s h

#print axioms sourcePairDensity_flipRowFrame
#print axioms sourcePairDensity_orientedPairFrame
end CubeSections.Certificates
