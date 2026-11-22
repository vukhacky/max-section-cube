import CubeSections.Analysis.SlabEnergyFromCost
import CubeSections.Integer.GramAngular

/-! Zero slab deficit admits an actual zero-cost Gaussian coupling without any
transport-inequality assumption. The graph coupling suffices because zero KL
identifies the transported law with the standard Gaussian. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace CubeSections

theorem frameTransportEntropy_eq_zero_of_deficit_zero {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hδ : frameSlabDeficit U r = 0) : frameTransportEntropy U r = 0 := by
  apply le_antisymm _ (frameTransportEntropy_nonneg U r)
  simpa only [hδ] using frameTransportEntropy_le_deficit U r hr

theorem frameTransportedLaw_eq_gaussian_of_deficit_zero {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hδ : frameSlabDeficit U r = 0) : frameTransportedLaw U r = stdGaussian (E k) := by
  letI := frameTransportedLaw_isProbabilityMeasure U r hr
  apply klDiv_eq_zero_iff.mp
  have hD := frameTransportEntropy_eq_zero_of_deficit_zero U r hr hδ
  change (klDiv (frameTransportedLaw U r) (stdGaussian (E k))).toReal = 0 at hD
  exact ((ENNReal.toReal_eq_zero_iff _).mp hD).resolve_right (frameTransport_klDiv_ne_top U r hr)

/-- The actual joint law of a uniform slab point and its Gaussian transport. -/
def frameGraphCoupling {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) : Measure (E k × E k) :=
  (frameSlabUniform U r).map (fun x => (x, frameGaussianTransport U r x))

theorem frameGraphCoupling_isProbabilityMeasure {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    IsProbabilityMeasure (frameGraphCoupling U r) := by
  letI := frameSlabUniform_isProbabilityMeasure U r hr
  unfold frameGraphCoupling
  infer_instance

theorem frameGraphCoupling_fst {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) :
    (frameGraphCoupling U r).map Prod.fst = frameSlabUniform U r := by
  rw [frameGraphCoupling, Measure.map_map measurable_fst (by fun_prop)]
  exact Measure.map_id

theorem frameGraphCoupling_snd {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) :
    (frameGraphCoupling U r).map Prod.snd = frameTransportedLaw U r := by
  rw [frameGraphCoupling, Measure.map_map measurable_snd (by fun_prop)]
  rfl

theorem frameGraphCoupling_output_cost_ae {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) :
    (fun p => ‖frameGaussianTransport U r p.1 - p.2‖ ^ 2) =ᵐ[frameGraphCoupling U r] (fun _ => (0 : ℝ)) := by
  apply (ae_map_iff (by fun_prop)
    (measurableSet_eq_fun (by fun_prop) measurable_const)).mpr
  filter_upwards with x
  simp

theorem frameGraphCoupling_output_cost_integrable {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) :
    Integrable (fun p => ‖frameGaussianTransport U r p.1 - p.2‖ ^ 2) (frameGraphCoupling U r) :=
  (integrable_zero (E k × E k) ℝ (frameGraphCoupling U r)).congr
    (frameGraphCoupling_output_cost_ae U r).symm

theorem frameGraphCoupling_output_cost {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) :
    (∫ p, ‖frameGaussianTransport U r p.1 - p.2‖ ^ 2 ∂frameGraphCoupling U r) = 0 := by
  rw [integral_congr_ae (frameGraphCoupling_output_cost_ae U r), integral_zero]

/-- The exact slab energy coupling in the zero-deficit case. No Talagrand premise
occurs: the transported law is Gaussian by the zero-KL characterization. -/
theorem slab_energy_of_zero_deficit {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (hδ : frameSlabDeficit U r = 0) :
    ∃ μ : Measure (E k × E k), IsProbabilityMeasure μ ∧
      MeasurePreserving Prod.fst μ (frameSlabUniform U r) ∧
      MeasurePreserving Prod.snd μ (stdGaussian (E k)) ∧
      Integrable (fun p => frameTransportEnergy U (slabQuantileOffset r)
        (frameQuantileCoordinates U r p.1) p.2) μ ∧
      (∫ p, frameTransportEnergy U (slabQuantileOffset r)
        (frameQuantileCoordinates U r p.1) p.2 ∂μ) ≤ 0 := by
  let μ := frameGraphCoupling U r
  have hfirst : MeasurePreserving Prod.fst μ (frameSlabUniform U r) :=
    ⟨measurable_fst, frameGraphCoupling_fst U r⟩
  have hG : MeasurePreserving Prod.snd μ (stdGaussian (E k)) :=
    ⟨measurable_snd, (frameGraphCoupling_snd U r).trans
      (frameTransportedLaw_eq_gaussian_of_deficit_zero U r hr hδ)⟩
  have hcost : (∫ p, ‖frameGaussianTransport U r p.1 - p.2‖ ^ 2 ∂μ) ≤
      2 * frameTransportEntropy U r := by
    rw [frameGraphCoupling_output_cost]
    exact mul_nonneg (by norm_num) (frameTransportEntropy_nonneg U r)
  obtain ⟨hI, hb⟩ := actual_slab_energy_of_output_cost U r hr μ hfirst
    (frameGraphCoupling_output_cost_integrable U r) hcost
  exact ⟨μ, frameGraphCoupling_isProbabilityMeasure U r hr, hfirst, hG, hI, by simpa only [hδ] using hb⟩

theorem gramAngularDefect_eq_zero_of_frameSlabDeficit_zero {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hδ : frameSlabDeficit U r = 0) : gramAngularDefect U = 0 := by
  obtain ⟨μ, hμ, hfirst, hG, hI, hb⟩ := slab_energy_of_zero_deficit U r hr hδ
  letI : IsProbabilityMeasure μ := hμ
  have h := frame_angular_bound_twenty_of_energy U μ Prod.snd hG
    (slabQuantileOffset r) (fun p => frameQuantileCoordinates U r p.1) 0 hI hb
  exact le_antisymm (by simpa only [gramAngularDefect, mul_zero] using h) (gramAngularDefect_nonneg U)

theorem gramAngularDefect_eq_zero_of_slabDeficit_zero {n k : ℕ}
    (U : Frame n k) (hδ : slabDeficit U = 0) : gramAngularDefect U = 0 := by
  apply gramAngularDefect_eq_zero_of_frameSlabDeficit_zero U (cubeFrameRadius U) (cubeFrameRadius_pos U)
  change frameSlabLogFactor U (cubeFrameRadius U) - Real.log (frameSlabVolume U (cubeFrameRadius U)) = 0
  rw [cubeSlabDeficit, hδ]

end CubeSections
