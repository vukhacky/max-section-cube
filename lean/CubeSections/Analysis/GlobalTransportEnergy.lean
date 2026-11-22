import CubeSections.Analysis.FrameGaussianEnergy
import CubeSections.Analysis.PotentialAmplitude

/-! The global angular estimate under Gaussian marginal and total-energy
hypotheses. The construction of the coupling is separate from this estimate. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CubeSections

def frameTransportEnergy {n k : ℕ} (U : Frame n k) (β T : Fin n → ℝ) (g : E k) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, gramProjection U i j ^ 2 *
      phi |(β i + T i ^ 2 / 2) - (β j + T j ^ 2 / 2)| +
    (1 / 2 : ℝ) * ∑ i, leverage U i * (T i - normalizedFrameCoordinate U i g) ^ 2

theorem frameTransportEnergy_nonneg {n k : ℕ} (U : Frame n k)
    (β T : Fin n → ℝ) (g : E k) : 0 ≤ frameTransportEnergy U β T g := by
  unfold frameTransportEnergy
  apply add_nonneg
  · apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (sq_nonneg _) (phi_nonneg _ (abs_nonneg _))
  · apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (leverage_nonneg U i) (sq_nonneg _))

theorem frame_score_energy_transfer {n k : ℕ} (U : Frame n k)
    (β T : Fin n → ℝ) (g : E k) :
    frameGaussianScoreEnergy U (fun i => Real.exp (2 * β i / 3)) g ≤
      (2 / 9 + 2 / (3 * Real.exp 1)) * frameTransportEnergy U β T g :=
  potential_score_transfer U β T (fun i => normalizedFrameCoordinate U i g)

/-- The exact global coefficient, conditional only on the displayed probabilistic
coupling and integrated total energy bound. -/
theorem frame_angular_bound_of_energy {n k : ℕ} (U : Frame n k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → E k) (hG : MeasurePreserving G μ (stdGaussian (E k)))
    (β : Fin n → ℝ) (T : Ω → Fin n → ℝ) (δ : ℝ)
    (hE : Integrable (fun ω => frameTransportEnergy U β (T ω) (G ω)) μ)
    (hbound : (∫ ω, frameTransportEnergy U β (T ω) (G ω) ∂μ) ≤ δ) :
    (k : ℝ) - ∑ i, ∑ j, gramProjection U i j ^ 4 / (leverage U i * leverage U j) ≤
      ((32 / gaussianSecondMoment) * (2 / 9 + 2 / (3 * Real.exp 1))) * δ := by
  let b : Fin n → ℝ := fun i => Real.exp (2 * β i / 3)
  have hb : ∀ i, 0 < b i := fun i => Real.exp_pos _
  have hobs := integrable_frameGaussianScoreEnergy U b
  have hobsμ : Integrable (fun ω => frameGaussianScoreEnergy U b (G ω)) μ :=
    hG.integrable_comp_of_integrable hobs
  have hAE : AEStronglyMeasurable (frameGaussianScoreEnergy U b) (μ.map G) := by
    rw [hG.map_eq]
    exact hobs.aestronglyMeasurable
  have hmoment := (integral_map hG.measurable.aemeasurable hAE).symm
  rw [hG.map_eq] at hmoment
  have hlow := frame_gaussian_energy_lower U b hb
  rw [← hmoment] at hlow
  let C : ℝ := 2 / 9 + 2 / (3 * Real.exp 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hup := integral_mono hobsμ (hE.const_mul C)
    (fun ω => frame_score_energy_transfer U β (T ω) (G ω))
  rw [integral_const_mul] at hup
  have htotal := hlow.trans (hup.trans (mul_le_mul_of_nonneg_left hbound hC))
  have hM : 0 < gaussianSecondMoment / 32 := by
    exact div_pos gaussianSecondMoment_pos (by norm_num)
  have hfinal :
      (k : ℝ) - ∑ i, ∑ j, gramProjection U i j ^ 4 / (leverage U i * leverage U j) ≤
        (C * δ) / (gaussianSecondMoment / 32) := by
    apply (le_div_iff₀ hM).mpr
    simpa only [mul_comm] using htotal
  have heq : (C * δ) / (gaussianSecondMoment / 32) =
      ((32 / gaussianSecondMoment) * C) * δ := by ring
  rw [heq] at hfinal
  exact hfinal

/-- The rational constant 20 under the same coupling and energy hypotheses. -/
theorem frame_angular_bound_twenty_of_energy {n k : ℕ} (U : Frame n k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → E k) (hG : MeasurePreserving G μ (stdGaussian (E k)))
    (β : Fin n → ℝ) (T : Ω → Fin n → ℝ) (δ : ℝ)
    (hE : Integrable (fun ω => frameTransportEnergy U β (T ω) (G ω)) μ)
    (hbound : (∫ ω, frameTransportEnergy U β (T ω) (G ω) ∂μ) ≤ δ) :
    (k : ℝ) - ∑ i, ∑ j, gramProjection U i j ^ 4 / (leverage U i * leverage U j) ≤
      20 * δ := by
  have hδ : 0 ≤ δ :=
    (integral_nonneg (fun ω => frameTransportEnergy_nonneg U β (T ω) (G ω))).trans hbound
  exact (frame_angular_bound_of_energy U μ G hG β T δ hE hbound).trans
    (mul_le_mul_of_nonneg_right global_gaussian_constant_le_twenty hδ)

end CubeSections
