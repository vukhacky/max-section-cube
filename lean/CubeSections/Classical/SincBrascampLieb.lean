import CubeSections.Classical.FourierDensity
import CubeSections.Classical.CodimensionReduction
import CubeSections.Geometry.ComplementDensity

/-! Specialized functional Brascamp--Lieb and its Fourier consequence.
The contract states both L¹ integrability and the sinc-product inequality.
Cube probability, complementary coarea and continuity at zero identify the
central section volume. `Classical.SincBLProved` supplies the functional bound.
-/
noncomputable section
open MeasureTheory

namespace CubeSections

/-- Specialized functional geometric Brascamp--Lieb for the sinc functions.
Zero complementary rows remain in both products and contribute the factor 1. -/
def SincBrascampLiebStatement : Prop :=
  ∀ (n d : ℕ), ∀ W : Frame n d, (∀ i, leverage W i ≤ 1/2) →
    Integrable (cubeAbsSincKernel W) ∧
      (∫ t : E d, cubeAbsSincKernel W t) ≤ sincProduct (leverage W)

theorem complementaryFrame_cubeUniform_density {n k : ℕ} (U : Frame n k) :
    (cubeUniformMeasure n).map (frameAdjoint (complementaryFrame U)) =
      volume.withDensity (fun y => ENNReal.ofReal (complementDensity U y)) := by
  rw [cubeUniformMeasure_eq_restrict]
  exact complementaryFrame_map_cube_real_density U

/-- Exact central-section Fourier inversion, conditional only on the displayed
L1 absolute sinc product. Every geometric density hypothesis is discharged. -/
theorem sectionVolume_eq_complementarySincIntegral {n k : ℕ} (U : Frame n k)
    (habs : Integrable (cubeAbsSincKernel (complementaryFrame U))) :
    sectionVolume U = ∫ t : E (n-k), cubeSincKernel (complementaryFrame U) t := by
  simpa only [complementDensity_zero] using
    cube_density_zero_eq_sincIntegral (complementaryFrame U) (complementDensity U)
      (measurable_complementDensity U) (complementDensity_nonneg U)
      (integrable_complementDensity U) (continuousAt_complementDensity_zero U)
      (complementaryFrame_cubeUniform_density U) habs

theorem sectionVolume_le_complementaryAbsSincIntegral {n k : ℕ} (U : Frame n k)
    (habs : Integrable (cubeAbsSincKernel (complementaryFrame U))) :
    sectionVolume U ≤ ∫ t : E (n-k), cubeAbsSincKernel (complementaryFrame U) t := by
  simpa only [complementDensity_zero] using
    cube_density_zero_le_absSincIntegral (complementaryFrame U) (complementDensity U)
      (measurable_complementDensity U) (complementDensity_nonneg U)
      (integrable_complementDensity U) (continuousAt_complementDensity_zero U)
      (complementaryFrame_cubeUniform_density U) habs

theorem classicalFourierProductBound_of_sincBrascampLieb
    (hBL : SincBrascampLiebStatement) : ClassicalFourierProductBound := by
  intro n k hk hkn hn U hc
  have hW (i : Fin n) : leverage (complementaryFrame U) i ≤ 1/2 := by
    rw [leverage_complementaryFrame]
    have := hc i
    linarith
  obtain ⟨hint, hbound⟩ := hBL n (n-k) (complementaryFrame U) hW
  have h := (sectionVolume_le_complementaryAbsSincIntegral U hint).trans hbound
  simpa only [sincProduct, leverage_complementaryFrame] using h

theorem classical_codimension_bound_of_sinc_inputs
    (hBall : StrictBallSincBound) (hBL : SincBrascampLiebStatement)
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k) (U : Frame n k) :
    sectionVolume U ≤ sharpValue n k :=
  classical_codimension_bound_of_analytic_inputs hBall
    (classicalFourierProductBound_of_sincBrascampLieb hBL) n k hk hkn hn U

theorem classical_equality_iff_of_sinc_inputs
    (hBall : StrictBallSincBound) (hBL : SincBrascampLiebStatement)
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 2*k)
    (U : Frame n k) (C : ℝ) (hangular : gramAngularDefect U ≤ C*slabDeficit U) :
    sectionVolume U = sharpValue n k ↔ IsBalancedSection U :=
  classical_equality_iff_of_analytic_inputs hBall
    (classicalFourierProductBound_of_sincBrascampLieb hBL) hk hkn hn U C hangular

#print axioms sectionVolume_eq_complementarySincIntegral
#print axioms classicalFourierProductBound_of_sincBrascampLieb
#print axioms classical_codimension_bound_of_sinc_inputs
#print axioms classical_equality_iff_of_sinc_inputs
end CubeSections
