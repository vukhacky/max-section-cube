import CubeSections.Analysis.PositiveGaussianCostProved
import CubeSections.Analysis.SlabEnergyFromCost

/-! The regular-density T2 theorem applied to the actual frame-transported law.
The regularity premise below is explicit. It is discharged separately by the
global frame-transport topology and density theorems; none of these reductions
asserts a general arbitrary-law Talagrand theorem. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory

namespace CubeSections

/-- The precise regular-density property needed for the actual frame law. -/
def FrameTransportRegularDensityStatement (k : ℕ) : Prop :=
  ∀ (n : ℕ) (U : Frame n k) (r : Fin n → ℝ), (∀ i, 0 < r i) →
    ∃ f : E k → ℝ, Continuous f ∧ GaussianDominated f ∧
      (∀ x, 0 < f x) ∧ (∫ x, f x) = 1 ∧
      frameTransportedLaw U r = euclideanDensityLaw f

/-- The actual frame-law instance, with both marginals and finite cost explicit. -/
def FrameGaussianQuadraticCostStatement (k : ℕ) : Prop :=
  ∀ (n : ℕ) (U : Frame n k) (r : Fin n → ℝ), (∀ i, 0 < r i) →
    ∃ π : Measure (E k × E k), IsProbabilityMeasure π ∧
      π.map Prod.fst = frameTransportedLaw U r ∧
      π.map Prod.snd = stdGaussian (E k) ∧
      Integrable (fun p => ‖p.1 - p.2‖ ^ 2) π ∧
      (∫ p, ‖p.1 - p.2‖ ^ 2 ∂π) ≤ 2 * frameTransportEntropy U r

/-- Density identification transfers the constructed regular-law coupling to
the actual frame law, including its actual KL divergence. -/
theorem frameGaussianQuadraticCost_of_regular_density {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) (f : E k → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (hm : (∫ x, f x) = 1)
    (hlaw : frameTransportedLaw U r = euclideanDensityLaw f) :
    ∃ π : Measure (E k × E k), IsProbabilityMeasure π ∧
      π.map Prod.fst = frameTransportedLaw U r ∧
      π.map Prod.snd = stdGaussian (E k) ∧
      Integrable (fun p => ‖p.1 - p.2‖ ^ 2) π ∧
      (∫ p, ‖p.1 - p.2‖ ^ 2 ∂π) ≤ 2 * frameTransportEntropy U r := by
  obtain ⟨π, hπ, hfirst, hsecond, hi, hcost⟩ :=
    gaussian_quadratic_transport_gaussianDominated k f hc hG hp hm
  rw [← hlaw] at hfirst hcost
  exact ⟨π, hπ, hfirst, hsecond, hi, hcost⟩

theorem frameGaussianQuadraticCost_of_frameTransportRegularDensity {k : ℕ}
    (hregular : FrameTransportRegularDensityStatement k) :
    FrameGaussianQuadraticCostStatement k := by
  intro n U r hr
  obtain ⟨f, hc, hG, hp, hm, hlaw⟩ := hregular n U r hr
  exact frameGaussianQuadraticCost_of_regular_density U r f hc hG hp hm hlaw

/-- Pulling back the actual output coupling proves the full slab-energy
contract, without an arbitrary-law Gaussian transport premise. -/
theorem slabGaussianEnergy_of_frameGaussianQuadraticCost {k : ℕ}
    (hcost : FrameGaussianQuadraticCostStatement k) : SlabGaussianEnergyStatement k := by
  intro n U r hr
  obtain ⟨π, hπprob, hπfirst, hπG, hπint, hπcost⟩ := hcost n U r hr
  letI : IsProbabilityMeasure π := hπprob
  let μ := framePullbackCoupling U r hr π
  have hμ : IsProbabilityMeasure μ := framePullbackCoupling_isProbabilityMeasure U r hr π
  have hfirst : MeasurePreserving Prod.fst μ (frameSlabUniform U r) :=
    ⟨measurable_fst, framePullbackCoupling_fst U r hr π hπfirst⟩
  have hG : MeasurePreserving Prod.snd μ (stdGaussian (E k)) :=
    ⟨measurable_snd, (framePullbackCoupling_snd U r hr π).trans hπG⟩
  have hbound : (∫ p, ‖frameGaussianTransport U r p.1 - p.2‖ ^ 2 ∂μ) ≤
      2 * frameTransportEntropy U r := by
    rw [framePullbackCoupling_cost U r hr π hπfirst]
    exact hπcost
  obtain ⟨hi, hb⟩ := actual_slab_energy_of_output_cost U r hr μ hfirst
    (integrable_framePullbackCoupling_cost U r hr π hπfirst hπG) hbound
  exact ⟨μ, hμ, hfirst, hG, hi, hb⟩

theorem slabGaussianEnergy_of_frameTransportRegularDensity {k : ℕ}
    (hregular : FrameTransportRegularDensityStatement k) : SlabGaussianEnergyStatement k :=
  slabGaussianEnergy_of_frameGaussianQuadraticCost
    (frameGaussianQuadraticCost_of_frameTransportRegularDensity hregular)

#print axioms frameGaussianQuadraticCost_of_regular_density
#print axioms frameGaussianQuadraticCost_of_frameTransportRegularDensity
#print axioms slabGaussianEnergy_of_frameGaussianQuadraticCost
#print axioms slabGaussianEnergy_of_frameTransportRegularDensity
end CubeSections
