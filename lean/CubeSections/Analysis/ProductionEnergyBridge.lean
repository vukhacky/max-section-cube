import CubeSections.Analysis.ClippedProduction
import CubeSections.Analysis.FrameLiftEnergy

/-! Angular estimates using the clipped determinant-production theorem.
The entropy decomposition, Gaussian coupling cost and required integrability
are explicit hypotheses of these implications. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CubeSections

theorem frameScoreProduction_le_determinantRemainder {n k : ℕ} (U : Frame n k)
    (β T : Fin n → ℝ) :
    frameScoreProduction U β T ≤
      determinantRemainder U (fun i => β i + T i ^ 2 / 2) :=
  gramPairProduction_le_determinantRemainder U (fun i => β i + T i ^ 2 / 2)

theorem frameScoreProduction_nonneg {n k : ℕ} (U : Frame n k)
    (β T : Fin n → ℝ) : 0 ≤ frameScoreProduction U β T :=
  gramPairProduction_nonneg U (fun i => β i + T i ^ 2 / 2)

theorem integrable_frameScoreProduction_of_determinant {n k : ℕ} (U : Frame n k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (β : Fin n → ℝ) (T : Ω → Fin n → ℝ)
    (hT : ∀ i, Measurable (fun ω => T ω i))
    (hJ : Integrable (fun ω => determinantRemainder U (fun i => β i + T ω i ^ 2 / 2)) μ) :
    Integrable (fun ω => frameScoreProduction U β (T ω)) μ := by
  apply hJ.mono'
  · unfold frameScoreProduction phi
    fun_prop
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (frameScoreProduction_nonneg U β (T ω))]
    exact frameScoreProduction_le_determinantRemainder U β (T ω)

/-- The global angular estimate with determinant production supplied by the
clipped-path theorem, conditional on the displayed entropy and transport bounds. -/
theorem frame_angular_bound_twenty_of_determinant_transport {n k : ℕ} (U : Frame n k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → E k) (hG : MeasurePreserving G μ (stdGaussian (E k)))
    (β : Fin n → ℝ) (T : Ω → Fin n → ℝ) (D δ : ℝ)
    (hT : ∀ i, Measurable (fun ω => T ω i))
    (hJ : Integrable (fun ω => determinantRemainder U (fun i => β i + T ω i ^ 2 / 2)) μ)
    (hres : Integrable (fun ω => ‖frameResidual U (liftedScores U (T ω))‖ ^ 2) μ)
    (herr : Integrable (fun ω => ‖frameAdjoint U (liftedScores U (T ω)) - G ω‖ ^ 2) μ)
    (hdecomp : δ = D + (∫ ω, determinantRemainder U (fun i => β i + T ω i ^ 2 / 2) ∂μ) +
      (1 / 2 : ℝ) * (∫ ω, ‖frameResidual U (liftedScores U (T ω))‖ ^ 2 ∂μ))
    (hcost : (∫ ω, ‖frameAdjoint U (liftedScores U (T ω)) - G ω‖ ^ 2 ∂μ) ≤ 2 * D) :
    (k : ℝ) - ∑ i, ∑ j, gramProjection U i j ^ 4 / (leverage U i * leverage U j) ≤
      20 * δ := by
  exact frame_angular_bound_twenty_of_entropy_decomposition U μ G hG β T
    (fun ω => determinantRemainder U (fun i => β i + T ω i ^ 2 / 2)) D δ
    (integrable_frameScoreProduction_of_determinant U μ β T hT hJ) hJ hres herr
    (fun ω => frameScoreProduction_le_determinantRemainder U β (T ω)) hdecomp hcost

end CubeSections
