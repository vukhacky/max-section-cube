import CubeSections.Analysis.TransportEntropy
import CubeSections.Analysis.TransportCoupling
import CubeSections.Analysis.SlabEnergyContract
import CubeSections.Analysis.ProductionEnergyBridge

/-! Slab energy from a Gaussian quadratic-cost coupling.

The general-law transport proposition below is used only as a hypothesis in
this module. The final maximal-section theorem uses the proved frame-law
instance from `Analysis.ActualGaussianCostProved`.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace CubeSections

/-- The general finite-dimensional Gaussian quadratic transport proposition,
expressed by a joint probability measure with prescribed marginals and a cost bound. -/
def GaussianQuadraticCostStatement (k : ℕ) : Prop :=
  ∀ ν : Measure (E k), IsProbabilityMeasure ν → MemLp id 2 ν →
    ν ≪ stdGaussian (E k) → klDiv ν (stdGaussian (E k)) ≠ ∞ →
    ∃ π : Measure (E k × E k), IsProbabilityMeasure π ∧
      π.map Prod.fst = ν ∧ π.map Prod.snd = stdGaussian (E k) ∧
      (∫ p, ‖p.1 - p.2‖ ^ 2 ∂π) ≤ 2 * (klDiv ν (stdGaussian (E k))).toReal

theorem frameTransportLogProduction_offset {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : E k) :
    frameTransportLogProduction U r x =
      determinantRemainder U (fun i => slabQuantileOffset r i + frameQuantileCoordinates U r x i ^ 2 / 2) := by
  unfold frameTransportLogProduction
  congr 1
  funext i
  exact frameQuantileSlope_log U r hr x i

private theorem integral_comp_measurePreserving_real {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    {μ : Measure Ω} {ν : Measure Λ} {f : Ω → Λ} (hf : MeasurePreserving f μ ν)
    (g : Λ → ℝ) (hg : Integrable g ν) : (∫ x, g (f x) ∂μ) = ∫ y, g y ∂ν := by
  have hgm : AEStronglyMeasurable g (μ.map f) := hf.map_eq.symm ▸ hg.aestronglyMeasurable
  rw [← integral_map hf.measurable.aemeasurable hgm, hf.map_eq]

/-- All entropy, production and moment inputs have been discharged. The only input
beyond the actual slab marginal is the displayed output coupling cost. -/
theorem actual_slab_energy_of_output_cost {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (μ : Measure (E k × E k))
    (hfirst : MeasurePreserving Prod.fst μ (frameSlabUniform U r))
    (hcost_int : Integrable (fun p => ‖frameGaussianTransport U r p.1 - p.2‖ ^ 2) μ)
    (hcost : (∫ p, ‖frameGaussianTransport U r p.1 - p.2‖ ^ 2 ∂μ) ≤ 2 * frameTransportEntropy U r) :
    Integrable (fun p => frameTransportEnergy U (slabQuantileOffset r)
      (frameQuantileCoordinates U r p.1) p.2) μ ∧
      (∫ p, frameTransportEnergy U (slabQuantileOffset r)
        (frameQuantileCoordinates U r p.1) p.2 ∂μ) ≤ frameSlabDeficit U r := by
  let T : E k × E k → Fin n → ℝ := fun p => frameQuantileCoordinates U r p.1
  let J : E k × E k → ℝ := fun p => frameTransportLogProduction U r p.1
  have hJ : Integrable J μ := hfirst.integrable_comp_of_integrable (integrable_frameTransportLogProduction U r hr)
  have hres : Integrable (fun p => ‖frameResidual U (liftedScores U (T p))‖ ^ 2) μ :=
    hfirst.integrable_comp_of_integrable (integrable_frameTransportResidualEnergy U r hr)
  have herr : Integrable (fun p => ‖frameAdjoint U (liftedScores U (T p)) - p.2‖ ^ 2) μ := by
    simpa only [T, ← frameGaussianTransport_eq_adjoint] using hcost_int
  have hJdet : Integrable (fun p => determinantRemainder U
      (fun i => slabQuantileOffset r i + T p i ^ 2 / 2)) μ := by
    apply hJ.congr
    filter_upwards with p
    exact frameTransportLogProduction_offset U r hr p.1
  have hP := integrable_frameScoreProduction_of_determinant U μ (slabQuantileOffset r) T
    (fun i => (measurable_frameQuantileCoordinate U r i).comp measurable_fst) hJdet
  have hL : Integrable (fun p => ‖liftedScores U (T p) - U p.2‖ ^ 2) μ := by
    apply (hres.add herr).congr
    filter_upwards with p
    simp only [Pi.add_apply]
    exact (frame_coupling_lift_identity U (liftedScores U (T p)) p.2).symm
  have hdecomp : frameSlabDeficit U r = frameTransportEntropy U r + (∫ p, J p ∂μ) +
      (1 / 2 : ℝ) * (∫ p, ‖frameResidual U (liftedScores U (T p))‖ ^ 2 ∂μ) := by
    change frameSlabDeficit U r = frameTransportEntropy U r +
      (∫ p, frameTransportLogProduction U r p.1 ∂μ) +
      (1 / 2 : ℝ) * (∫ p, frameTransportResidualEnergy U r p.1 ∂μ)
    rw [integral_comp_measurePreserving_real hfirst _ (integrable_frameTransportLogProduction U r hr),
      integral_comp_measurePreserving_real hfirst _ (integrable_frameTransportResidualEnergy U r hr)]
    exact frameTransport_entropy_decomposition U r hr
  have hcost' : (∫ p, ‖frameAdjoint U (liftedScores U (T p)) - p.2‖ ^ 2 ∂μ) ≤
      2 * frameTransportEntropy U r := by
    simpa only [T, ← frameGaussianTransport_eq_adjoint] using hcost
  have hLbound := integral_frame_coupling_lift_le U μ (fun p => liftedScores U (T p)) Prod.snd
    hres herr (frameTransportEntropy U r) (∫ p, J p ∂μ) (frameSlabDeficit U r) hdecomp hcost'
  exact integral_frameTransportEnergy_le U μ Prod.snd (slabQuantileOffset r) T J
    (frameSlabDeficit U r) hP hJ hL
    (fun p => by
      dsimp only [J]
      rw [frameTransportLogProduction_offset U r hr]
      exact frameScoreProduction_le_determinantRemainder U _ _) hLbound

/-- Slab energy follows from Gaussian quadratic transport via inverse lifting
and the entropy and moment identities proved above. -/
theorem slabGaussianEnergy_of_gaussianQuadraticCost {k : ℕ}
    (hTal : GaussianQuadraticCostStatement k) : SlabGaussianEnergyStatement k := by
  intro n U r hr
  obtain ⟨π, hπprob, hπfirst, hπG, hπcost⟩ := hTal (frameTransportedLaw U r)
    (frameTransportedLaw_isProbabilityMeasure U r hr) (memLp_id_frameTransportedLaw_two U r hr)
    (frameTransportedLaw_absolutelyContinuous_gaussian U r hr) (frameTransport_klDiv_ne_top U r hr)
  letI : IsProbabilityMeasure π := hπprob
  let μ := framePullbackCoupling U r hr π
  have hμ : IsProbabilityMeasure μ := framePullbackCoupling_isProbabilityMeasure U r hr π
  have hfirst : MeasurePreserving Prod.fst μ (frameSlabUniform U r) :=
    ⟨measurable_fst, framePullbackCoupling_fst U r hr π hπfirst⟩
  have hG : MeasurePreserving Prod.snd μ (stdGaussian (E k)) :=
    ⟨measurable_snd, (framePullbackCoupling_snd U r hr π).trans hπG⟩
  have hcost : (∫ p, ‖frameGaussianTransport U r p.1 - p.2‖ ^ 2 ∂μ) ≤
      2 * frameTransportEntropy U r := by
    rw [framePullbackCoupling_cost U r hr π hπfirst]
    exact hπcost
  obtain ⟨hi, hb⟩ := actual_slab_energy_of_output_cost U r hr μ hfirst
    (integrable_framePullbackCoupling_cost U r hr π hπfirst hπG) hcost
  exact ⟨μ, hμ, hfirst, hG, hi, hb⟩

end CubeSections
