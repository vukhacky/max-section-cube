import CubeSections.Analysis.ActualGaussianCostProved

/-! The manuscript's actual lifted Gaussian coupling, retaining the determinant
production term in the sharp Pythagorean cost budget. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace CubeSections

private theorem integral_comp_actual_coupling {Ω Λ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Λ] {μ : Measure Ω} {ν : Measure Λ}
    {f : Ω → Λ} (hf : MeasurePreserving f μ ν)
    (g : Λ → ℝ) (hg : Integrable g ν) :
    (∫ x, g (f x) ∂μ) = ∫ y, g y ∂ν := by
  have hgm : AEStronglyMeasurable g (μ.map f) := hf.map_eq.symm ▸ hg.aestronglyMeasurable
  rw [← integral_map hf.measurable.aemeasurable hgm, hf.map_eq]

/-- For every actual positive-width slab body there is an actual coupling of
its uniform law with the standard Gaussian whose lifted cost is integrable
and at most twice deficit minus integrated determinant production. -/
theorem exists_actual_lifted_gaussian_coupling {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ μ : Measure (E k × E k), IsProbabilityMeasure μ ∧
      MeasurePreserving Prod.fst μ (frameSlabUniform U r) ∧
      MeasurePreserving Prod.snd μ (stdGaussian (E k)) ∧
      Integrable (fun p =>
        ‖liftedScores U (frameQuantileCoordinates U r p.1) - U p.2‖ ^ 2) μ ∧
      (∫ p, ‖liftedScores U (frameQuantileCoordinates U r p.1) - U p.2‖ ^ 2 ∂μ) ≤
        2 * (frameSlabDeficit U r -
          ∫ x, frameTransportLogProduction U r x ∂frameSlabUniform U r) := by
  obtain ⟨π, hπprob, hπfirst, hπG, hπint, hπcost⟩ := frameGaussianQuadraticCost k n U r hr
  letI : IsProbabilityMeasure π := hπprob
  let μ := framePullbackCoupling U r hr π
  have hμ : IsProbabilityMeasure μ := framePullbackCoupling_isProbabilityMeasure U r hr π
  have hfirst : MeasurePreserving Prod.fst μ (frameSlabUniform U r) :=
    ⟨measurable_fst, framePullbackCoupling_fst U r hr π hπfirst⟩
  have hG : MeasurePreserving Prod.snd μ (stdGaussian (E k)) :=
    ⟨measurable_snd, (framePullbackCoupling_snd U r hr π).trans hπG⟩
  let b : E k × E k → E n := fun p => liftedScores U (frameQuantileCoordinates U r p.1)
  have hres : Integrable (fun p => ‖frameResidual U (b p)‖ ^ 2) μ :=
    hfirst.integrable_comp_of_integrable (integrable_frameTransportResidualEnergy U r hr)
  have herr : Integrable (fun p => ‖frameAdjoint U (b p) - p.2‖ ^ 2) μ := by
    simpa only [b, ← frameGaussianTransport_eq_adjoint] using
      integrable_framePullbackCoupling_cost U r hr π hπfirst hπG
  have hL : Integrable (fun p => ‖b p - U p.2‖ ^ 2) μ := by
    apply (hres.add herr).congr
    filter_upwards with p
    simp only [Pi.add_apply]
    exact (frame_coupling_lift_identity U (b p) p.2).symm
  have hres_eq : (∫ p, ‖frameResidual U (b p)‖ ^ 2 ∂μ) =
      ∫ x, frameTransportResidualEnergy U r x ∂frameSlabUniform U r :=
    integral_comp_actual_coupling hfirst _ (integrable_frameTransportResidualEnergy U r hr)
  have hdecomp : frameSlabDeficit U r = frameTransportEntropy U r +
      (∫ x, frameTransportLogProduction U r x ∂frameSlabUniform U r) +
      (1 / 2 : ℝ) * (∫ p, ‖frameResidual U (b p)‖ ^ 2 ∂μ) := by
    rw [hres_eq]
    exact frameTransport_entropy_decomposition U r hr
  have hcost : (∫ p, ‖frameAdjoint U (b p) - p.2‖ ^ 2 ∂μ) ≤
      2 * frameTransportEntropy U r := by
    have hpull : (∫ p, ‖frameGaussianTransport U r p.1 - p.2‖ ^ 2 ∂μ) ≤
        2 * frameTransportEntropy U r := by
      rw [framePullbackCoupling_cost U r hr π hπfirst]
      exact hπcost
    simpa only [b, ← frameGaussianTransport_eq_adjoint] using hpull
  exact ⟨μ, hμ, hfirst, hG, hL,
    integral_frame_coupling_lift_le U μ b Prod.snd hres herr
      (frameTransportEntropy U r)
      (∫ x, frameTransportLogProduction U r x ∂frameSlabUniform U r)
      (frameSlabDeficit U r) hdecomp hcost⟩

#print axioms exists_actual_lifted_gaussian_coupling
end CubeSections
