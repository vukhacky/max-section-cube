import CubeSections.Certificates.FrameIncidence
import CubeSections.Analysis.ProductionEnergyBridge

/-! Incidence under the same explicit entropy/lift contract as the global
angular theorem. The scalar determinant production is already proved; the
entropy decomposition and Gaussian coupling cost remain visible hypotheses.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CubeSections.Certificates

theorem frame_incidence_bound_of_lifted_cost {n k : ℕ} (U : Frame n k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → E k) (hG : MeasurePreserving G μ (stdGaussian (E k)))
    (β : Fin n → ℝ) (T : Ω → Fin n → ℝ) (J : Ω → ℝ) (δ : ℝ)
    (hP : Integrable (fun ω => frameScoreProduction U β (T ω)) μ)
    (hJ : Integrable J μ)
    (hL : Integrable (fun ω => ‖liftedScores U (T ω)-U (G ω)‖^2) μ)
    (hprod : ∀ ω, frameScoreProduction U β (T ω) ≤ J ω)
    (hcost : (∫ ω, ‖liftedScores U (T ω)-U (G ω)‖^2 ∂μ) ≤
      2*(δ-∫ ω, J ω ∂μ)) : framePairIncidence U ≤ δ := by
  obtain ⟨hE,hbound⟩ := integral_frameTransportEnergy_le U μ G β T J δ hP hJ hL hprod hcost
  exact frame_incidence_bound_of_energy U μ G hG β T δ hE hbound

theorem frame_incidence_bound_of_entropy_decomposition {n k : ℕ} (U : Frame n k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → E k) (hG : MeasurePreserving G μ (stdGaussian (E k)))
    (β : Fin n → ℝ) (T : Ω → Fin n → ℝ) (J : Ω → ℝ) (D δ : ℝ)
    (hP : Integrable (fun ω => frameScoreProduction U β (T ω)) μ)
    (hJ : Integrable J μ)
    (hres : Integrable (fun ω => ‖frameResidual U (liftedScores U (T ω))‖^2) μ)
    (herr : Integrable (fun ω => ‖frameAdjoint U (liftedScores U (T ω))-G ω‖^2) μ)
    (hprod : ∀ ω, frameScoreProduction U β (T ω) ≤ J ω)
    (hdecomp : δ = D+(∫ ω, J ω ∂μ)+
      (1/2 : ℝ)*(∫ ω, ‖frameResidual U (liftedScores U (T ω))‖^2 ∂μ))
    (hcost : (∫ ω, ‖frameAdjoint U (liftedScores U (T ω))-G ω‖^2 ∂μ) ≤ 2*D) :
    framePairIncidence U ≤ δ := by
  have hL : Integrable (fun ω => ‖liftedScores U (T ω)-U (G ω)‖^2) μ := by
    apply (hres.add herr).congr
    exact Filter.Eventually.of_forall (fun ω =>
      (frame_coupling_lift_identity U (liftedScores U (T ω)) (G ω)).symm)
  have hbound := integral_frame_coupling_lift_le U μ
    (fun ω => liftedScores U (T ω)) G hres herr D (∫ ω, J ω ∂μ) δ hdecomp hcost
  exact frame_incidence_bound_of_lifted_cost U μ G hG β T J δ hP hJ hL hprod hbound

/-- Determinant production is discharged here. D is an explicit scalar; no claim
that D is a KL divergence or that a suitable coupling exists is made by this theorem. -/
theorem frame_incidence_bound_of_determinant_transport {n k : ℕ} (U : Frame n k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → E k) (hG : MeasurePreserving G μ (stdGaussian (E k)))
    (β : Fin n → ℝ) (T : Ω → Fin n → ℝ) (D δ : ℝ)
    (hT : ∀ i, Measurable (fun ω => T ω i))
    (hJ : Integrable (fun ω => determinantRemainder U (fun i => β i+T ω i^2/2)) μ)
    (hres : Integrable (fun ω => ‖frameResidual U (liftedScores U (T ω))‖^2) μ)
    (herr : Integrable (fun ω => ‖frameAdjoint U (liftedScores U (T ω))-G ω‖^2) μ)
    (hdecomp : δ = D+(∫ ω, determinantRemainder U (fun i => β i+T ω i^2/2) ∂μ)+
      (1/2 : ℝ)*(∫ ω, ‖frameResidual U (liftedScores U (T ω))‖^2 ∂μ))
    (hcost : (∫ ω, ‖frameAdjoint U (liftedScores U (T ω))-G ω‖^2 ∂μ) ≤ 2*D) :
    framePairIncidence U ≤ δ := by
  exact frame_incidence_bound_of_entropy_decomposition U μ G hG β T
    (fun ω => determinantRemainder U (fun i => β i+T ω i^2/2)) D δ
    (integrable_frameScoreProduction_of_determinant U μ β T hT hJ) hJ hres herr
    (fun ω => frameScoreProduction_le_determinantRemainder U β (T ω)) hdecomp hcost

#print axioms frame_incidence_bound_of_entropy_decomposition
#print axioms frame_incidence_bound_of_determinant_transport
end CubeSections.Certificates
