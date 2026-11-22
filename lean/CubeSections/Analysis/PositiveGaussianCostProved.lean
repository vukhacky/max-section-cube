import CubeSections.Analysis.GaussianCostTensorization
import CubeSections.Analysis.GaussianConditionalEntropy
import CubeSections.Analysis.ScalarGaussianDensity
import CubeSections.Analysis.PositiveGaussianTalagrandProved

/-! Gaussian quadratic-cost transport for every continuous strictly positive
Gaussian-dominated probability density in finite-dimensional Euclidean space.
This is a restricted regular-law theorem. It does not assert the separate
arbitrary-law GaussianQuadraticCostStatement or an approximation principle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace CubeSections

theorem euclideanConditionalInverse_cost_le_klDiv {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x) (x : E n) :
    (∫ z, (euclideanConditionalInverse f hc hG hp x z-z)^2 ∂gaussianReal 0 1) ≤
      2*euclideanConditionalKL f x := by
  obtain ⟨C,a,hC,ha,hbound⟩ := euclideanConditionalDensity_gaussian_bound f hc hG hp x
  have hregular := scalarGaussianBound_memLp_klDiv_finite
    (continuous_euclideanConditionalSlice f hc x)
    (euclideanConditionalDensity_pos f hc hG hp x)
    (integral_euclideanConditionalDensity f hc hG hp x) C a hC ha hbound
  exact positiveDensityInverse_cost_le_twice_klDiv (euclideanConditionalDensity f x)
    (continuous_euclideanConditionalSlice f hc x)
    (integrable_euclideanConditionalSlice f hc hG x)
    (euclideanConditionalDensity_pos f hc hG hp x)
    (integral_euclideanConditionalDensity f hc hG hp x) hregular.1 hregular.2

/-- A finite-dimensional probability coupling with finite quadratic cost for
the stated continuous positive Gaussian-dominated densities. -/
theorem gaussian_quadratic_transport_gaussianDominated (n : ℕ) :
    ∀ (f : E n → ℝ) (hc : Continuous f) (hG : GaussianDominated f)
      (hp : ∀ x, 0 < f x) (hm : (∫ x, f x)=1),
      ∃ π : Measure (E n × E n), IsProbabilityMeasure π ∧
        π.map Prod.fst = euclideanDensityLaw f ∧ π.map Prod.snd = stdGaussian (E n) ∧
        Integrable (fun p => ‖p.1-p.2‖^2) π ∧
        (∫ p, ‖p.1-p.2‖^2 ∂π) ≤ 2*(klDiv (euclideanDensityLaw f) (stdGaussian (E n))).toReal := by
  induction n with
  | zero =>
    intro f hc hG hp hm
    letI := euclideanDensityLaw_probability (hG.integrable hc) hp hm
    refine ⟨(euclideanDensityLaw f).prod (stdGaussian (E 0)), inferInstance, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · exact integrable_joint_quadratic_cost _ _ _ (by simp) (by simp)
        (hG.integrable_secondMoment hc hp) (integrable_norm_sq_stdGaussian 0)
    · have hzero : (fun p : E 0 × E 0 => ‖p.1-p.2‖^2) = fun _ => 0 := by
        funext p
        have heq : p.1=p.2 := Subsingleton.elim _ _
        simp [heq]
      rw [hzero, integral_zero]
      positivity
  | succ n ih =>
    intro f hc hG hp hm
    have hMc := continuous_euclideanMarginal f hc hG
    have hMG := gaussianDominated_euclideanMarginal f hc hG
    have hMp := euclideanMarginal_pos f hc hG hp
    have hMm : (∫ x, euclideanMarginal f x)=1 := (integral_euclideanMarginal f hc hG).trans hm
    obtain ⟨π,hπ,hfst,hsnd,hI,hbound⟩ := ih (euclideanMarginal f) hMc hMG hMp hMm
    letI : IsProbabilityMeasure π := hπ
    have hsecond := hG.integrable_secondMoment hc hp
    refine ⟨tensorizedGaussianCoupling f hc hG hp π,
      tensorizedGaussianCoupling_probability f hc hG hp π,
      tensorizedGaussianCoupling_fst f hc hG hp π hfst,
      tensorizedGaussianCoupling_snd f hc hG hp π hsnd,
      tensorizedGaussianCoupling_integrable_cost f hc hG hp π hfst hsnd hsecond, ?_⟩
    exact tensorizedGaussianCoupling_cost_le f hc hG hp π hfst hsnd hsecond hI
      (klDiv (euclideanDensityLaw (euclideanMarginal f)) (stdGaussian (E n))).toReal
      (klDiv (euclideanDensityLaw f) (stdGaussian (E (n+1)))).toReal
      (euclideanConditionalKL f) (integrable_euclideanConditionalKL f hc hG hp hm) hbound
      (euclideanConditionalInverse_cost_le_klDiv f hc hG hp)
      (euclideanConditionalKL_chain f hc hG hp hm)

#print axioms euclideanConditionalInverse_cost_le_klDiv
#print axioms gaussian_quadratic_transport_gaussianDominated
end CubeSections
