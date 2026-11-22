import CubeSections.Analysis.GaussianTest
import CubeSections.Certificates.PairEnergyBridge

/-! The exact certificate cost is bounded by the actual integrated pair energy.
The Gaussian marginal and integrability hypotheses are explicit.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace
namespace CubeSections.Certificates

theorem pairAngularCost_le_integral_potentialPairEnergy
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → F) (hG : MeasurePreserving G μ (stdGaussian F))
    (u v : F) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (A B β η : ℝ) (hA : A < 1) (hB : B < 1)
    (hβ : 0 ≤ β) (hη : 0 ≤ η) (hzero : β = 0 ∨ η = 0)
    (T S : Ω → ℝ)
    (hE : Integrable (fun ω => CubeSections.potentialPairEnergy A B β η (T ω) (S ω)
      ⟪u, G ω⟫_ℝ ⟪v, G ω⟫_ℝ) μ) :
    pairAngularCost A B (⟪u,v⟫_ℝ^2) ≤
      ∫ ω, CubeSections.potentialPairEnergy A B β η (T ω) (S ω)
        ⟪u, G ω⟫_ℝ ⟪v, G ω⟫_ℝ ∂μ := by
  rw [pairAngularCost_eq_gaussian_quotient]
  exact CubeSections.integral_potentialPairEnergy_lower μ G hG u v hu hv
    A B β η hA hB hβ hη hzero T S hE

#print axioms pairAngularCost_le_integral_potentialPairEnergy
end CubeSections.Certificates
