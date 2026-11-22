import CubeSections.Analysis.GlobalTransportEnergy
import CubeSections.Analysis.CouplingLift

/-! Exact bridge from leverage-weighted coordinate errors to the orthogonal
coupling lift. The production bound, entropy identity, and Gaussian coupling
cost remain explicit hypotheses. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CubeSections

def liftedScores {n k : ℕ} (U : Frame n k) (T : Fin n → ℝ) : E n :=
  WithLp.toLp 2 (fun i => Real.sqrt (leverage U i) * T i)

@[simp] theorem liftedScores_apply {n k : ℕ} (U : Frame n k) (T : Fin n → ℝ) (i : Fin n) :
    liftedScores U T i = Real.sqrt (leverage U i) * T i := rfl

theorem normalizedFrameCoordinate_scaled {n k : ℕ} (U : Frame n k) (i : Fin n) (g : E k) :
    Real.sqrt (leverage U i) * normalizedFrameCoordinate U i g = (U g) i := by
  by_cases hi : 0 < leverage U i
  · have hs : Real.sqrt (leverage U i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hi)
    rw [normalizedFrameCoordinate_eq]
    field_simp
  · have hi₀ : leverage U i = 0 := le_antisymm (le_of_not_gt hi) (leverage_nonneg U i)
    have hrow : rowVector U i = 0 := by
      apply norm_eq_zero.mp
      rw [rowVector_norm, hi₀, Real.sqrt_zero]
    rw [← rowVector_inner U i g, hrow]
    simp [hi₀]

theorem liftedScores_distance_sq {n k : ℕ} (U : Frame n k) (T : Fin n → ℝ) (g : E k) :
    ‖liftedScores U T - U g‖ ^ 2 =
      ∑ i, leverage U i * (T i - normalizedFrameCoordinate U i g) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  change (Real.sqrt (leverage U i) * T i - (U g) i) ^ 2 = _
  rw [← normalizedFrameCoordinate_scaled U i g, ← mul_sub, mul_pow,
    Real.sq_sqrt (leverage_nonneg U i)]

def frameScoreProduction {n k : ℕ} (U : Frame n k) (β T : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, gramProjection U i j ^ 2 *
    phi |(β i + T i ^ 2 / 2) - (β j + T j ^ 2 / 2)|

theorem frameTransportEnergy_eq_production_add_cost {n k : ℕ} (U : Frame n k)
    (β T : Fin n → ℝ) (g : E k) :
    frameTransportEnergy U β T g =
      frameScoreProduction U β T + (1 / 2 : ℝ) * ‖liftedScores U T - U g‖ ^ 2 := by
  rw [liftedScores_distance_sq]
  rfl

theorem integral_frameTransportEnergy_le {n k : ℕ} (U : Frame n k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G : Ω → E k) (β : Fin n → ℝ) (T : Ω → Fin n → ℝ) (J : Ω → ℝ) (δ : ℝ)
    (hP : Integrable (fun ω => frameScoreProduction U β (T ω)) μ)
    (hJ : Integrable J μ)
    (hL : Integrable (fun ω => ‖liftedScores U (T ω) - U (G ω)‖ ^ 2) μ)
    (hprod : ∀ ω, frameScoreProduction U β (T ω) ≤ J ω)
    (hcost : (∫ ω, ‖liftedScores U (T ω) - U (G ω)‖ ^ 2 ∂μ) ≤
      2 * (δ - ∫ ω, J ω ∂μ)) :
    Integrable (fun ω => frameTransportEnergy U β (T ω) (G ω)) μ ∧
      (∫ ω, frameTransportEnergy U β (T ω) (G ω) ∂μ) ≤ δ := by
  constructor
  · apply (hP.add (hL.const_mul (1 / 2 : ℝ))).congr
    filter_upwards with ω
    simp only [Pi.add_apply, frameTransportEnergy_eq_production_add_cost]
  · simp_rw [frameTransportEnergy_eq_production_add_cost]
    rw [integral_add hP (hL.const_mul (1 / 2 : ℝ)), integral_const_mul]
    have h := integral_mono hP hJ hprod
    linarith

theorem frame_angular_bound_twenty_of_lifted_cost {n k : ℕ} (U : Frame n k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → E k) (hG : MeasurePreserving G μ (stdGaussian (E k)))
    (β : Fin n → ℝ) (T : Ω → Fin n → ℝ) (J : Ω → ℝ) (δ : ℝ)
    (hP : Integrable (fun ω => frameScoreProduction U β (T ω)) μ)
    (hJ : Integrable J μ)
    (hL : Integrable (fun ω => ‖liftedScores U (T ω) - U (G ω)‖ ^ 2) μ)
    (hprod : ∀ ω, frameScoreProduction U β (T ω) ≤ J ω)
    (hcost : (∫ ω, ‖liftedScores U (T ω) - U (G ω)‖ ^ 2 ∂μ) ≤
      2 * (δ - ∫ ω, J ω ∂μ)) :
    (k : ℝ) - ∑ i, ∑ j, gramProjection U i j ^ 4 / (leverage U i * leverage U j) ≤
      20 * δ := by
  obtain ⟨hE, hbound⟩ := integral_frameTransportEnergy_le U μ G β T J δ hP hJ hL hprod hcost
  exact frame_angular_bound_twenty_of_energy U μ G hG β T δ hE hbound

/-- The algebraic entropy/lift endpoint. This theorem neither constructs the
Gaussian coupling nor asserts that its real parameter D is a KL divergence. -/
theorem frame_angular_bound_twenty_of_entropy_decomposition {n k : ℕ} (U : Frame n k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → E k) (hG : MeasurePreserving G μ (stdGaussian (E k)))
    (β : Fin n → ℝ) (T : Ω → Fin n → ℝ) (J : Ω → ℝ) (D δ : ℝ)
    (hP : Integrable (fun ω => frameScoreProduction U β (T ω)) μ)
    (hJ : Integrable J μ)
    (hres : Integrable (fun ω => ‖frameResidual U (liftedScores U (T ω))‖ ^ 2) μ)
    (herr : Integrable (fun ω => ‖frameAdjoint U (liftedScores U (T ω)) - G ω‖ ^ 2) μ)
    (hprod : ∀ ω, frameScoreProduction U β (T ω) ≤ J ω)
    (hdecomp : δ = D + (∫ ω, J ω ∂μ) +
      (1 / 2 : ℝ) * (∫ ω, ‖frameResidual U (liftedScores U (T ω))‖ ^ 2 ∂μ))
    (hcost : (∫ ω, ‖frameAdjoint U (liftedScores U (T ω)) - G ω‖ ^ 2 ∂μ) ≤ 2 * D) :
    (k : ℝ) - ∑ i, ∑ j, gramProjection U i j ^ 4 / (leverage U i * leverage U j) ≤
      20 * δ := by
  have hL : Integrable (fun ω => ‖liftedScores U (T ω) - U (G ω)‖ ^ 2) μ := by
    apply (hres.add herr).congr
    exact Filter.Eventually.of_forall (fun ω =>
      (frame_coupling_lift_identity U (liftedScores U (T ω)) (G ω)).symm)
  have hbound := integral_frame_coupling_lift_le U μ
    (fun ω => liftedScores U (T ω)) G hres herr D (∫ ω, J ω ∂μ) δ hdecomp hcost
  exact frame_angular_bound_twenty_of_lifted_cost U μ G hG β T J δ hP hJ hL hprod hbound

end CubeSections
