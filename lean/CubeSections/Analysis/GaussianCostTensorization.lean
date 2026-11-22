import CubeSections.Analysis.PositiveGaussianCost

/-! Coupling-level tensorization using the actual conditional Gaussian inverse.
An arbitrary lower-dimensional coupling is sufficient; no deterministic Monge
map or independence of the target coordinates is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CubeSections

def tensorizedGaussianPair {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (p : (E n × E n) × ℝ) : E (n+1) × E (n+1) :=
  (euclideanSuccJoin n (p.1.1,euclideanConditionalInverse f hc hG hp p.1.1 p.2),
    euclideanSuccJoin n (p.1.2,p.2))

theorem measurable_tensorizedGaussianPair {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x) :
    Measurable (tensorizedGaussianPair f hc hG hp) :=
  ((continuous_euclideanSuccJoin n).measurable.comp
    ((measurable_triangularConditionalInverse f hc hG hp).comp
      (measurable_fst.prodMap measurable_id))).prodMk
    ((continuous_euclideanSuccJoin n).measurable.comp (measurable_snd.prodMap measurable_id))

def tensorizedGaussianCoupling {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (π : Measure (E n × E n)) : Measure (E (n+1) × E (n+1)) :=
  (π.prod (gaussianReal 0 1)).map (tensorizedGaussianPair f hc hG hp)

theorem tensorizedGaussianCoupling_probability {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (π : Measure (E n × E n)) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (tensorizedGaussianCoupling f hc hG hp π) := by
  constructor
  rw [tensorizedGaussianCoupling, Measure.map_apply (measurable_tensorizedGaussianPair f hc hG hp)
    MeasurableSet.univ, Set.preimage_univ, measure_univ]

theorem tensorizedGaussianCoupling_fst {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (π : Measure (E n × E n))
    (hfst : π.map Prod.fst = euclideanDensityLaw (euclideanMarginal f)) :
    (tensorizedGaussianCoupling f hc hG hp π).map Prod.fst = euclideanDensityLaw f := by
  have hprod : (π.prod (gaussianReal 0 1)).map (Prod.map Prod.fst id) =
      (euclideanDensityLaw (euclideanMarginal f)).prod (gaussianReal 0 1) := by
    rw [← Measure.map_prod_map _ _ measurable_fst measurable_id, Measure.map_id, hfst]
  rw [tensorizedGaussianCoupling, Measure.map_map measurable_fst
    (measurable_tensorizedGaussianPair f hc hG hp)]
  change (π.prod (gaussianReal 0 1)).map
    (euclideanSuccJoin n ∘ triangularConditionalInverse f hc hG hp ∘ Prod.map Prod.fst id) = _
  rw [← Measure.map_map (continuous_euclideanSuccJoin n).measurable
      ((measurable_triangularConditionalInverse f hc hG hp).comp
        (measurable_fst.prodMap measurable_id)),
    ← Measure.map_map (measurable_triangularConditionalInverse f hc hG hp)
      (measurable_fst.prodMap measurable_id), hprod, euclideanDensityLaw,
    triangularConditionalInverse_map_law, euclideanSuccJoin_density_map f hc.measurable]

theorem tensorizedGaussianCoupling_snd {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (π : Measure (E n × E n)) (hsnd : π.map Prod.snd = stdGaussian (E n)) :
    (tensorizedGaussianCoupling f hc hG hp π).map Prod.snd = stdGaussian (E (n+1)) := by
  have hprod : (π.prod (gaussianReal 0 1)).map (Prod.map Prod.snd id) =
      (stdGaussian (E n)).prod (gaussianReal 0 1) := by
    rw [← Measure.map_prod_map _ _ measurable_snd measurable_id, Measure.map_id, hsnd]
  rw [tensorizedGaussianCoupling, Measure.map_map measurable_snd
    (measurable_tensorizedGaussianPair f hc hG hp)]
  change (π.prod (gaussianReal 0 1)).map
    (euclideanSuccJoin n ∘ Prod.map Prod.snd id) = _
  rw [← Measure.map_map (continuous_euclideanSuccJoin n).measurable
    (measurable_snd.prodMap measurable_id), hprod, euclideanSuccJoin_gaussian_map]

theorem tensorizedGaussianPair_cost {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (p : (E n × E n) × ℝ) :
    ‖(tensorizedGaussianPair f hc hG hp p).1-(tensorizedGaussianPair f hc hG hp p).2‖^2 =
      ‖p.1.1-p.1.2‖^2 + (euclideanConditionalInverse f hc hG hp p.1.1 p.2-p.2)^2 :=
  euclideanSuccJoin_sub_norm_sq n _ _ _ _

theorem measurable_conditionalGaussianCost {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x) :
    Measurable (fun x : E n => ∫ z, (euclideanConditionalInverse f hc hG hp x z-z)^2
      ∂gaussianReal 0 1) := by
  have hm : Measurable (fun p : E n × ℝ => (euclideanConditionalInverse f hc hG hp p.1 p.2-p.2)^2) :=
    ((measurable_euclideanConditionalInverse f hc hG hp).sub measurable_snd).pow_const 2
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem tensorizedGaussianCoupling_cost {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (π : Measure (E n × E n)) [IsProbabilityMeasure π]
    (hfst : π.map Prod.fst = euclideanDensityLaw (euclideanMarginal f))
    (hI : Integrable (fun p : E n × E n => ‖p.1-p.2‖^2) π)
    (hJ : Integrable (fun p : (E n × E n) × ℝ =>
      (euclideanConditionalInverse f hc hG hp p.1.1 p.2-p.2)^2) (π.prod (gaussianReal 0 1))) :
    (∫ p, ‖p.1-p.2‖^2 ∂tensorizedGaussianCoupling f hc hG hp π) =
      (∫ p, ‖p.1-p.2‖^2 ∂π) +
      ∫ x, ∫ z, (euclideanConditionalInverse f hc hG hp x z-z)^2
        ∂gaussianReal 0 1 ∂euclideanDensityLaw (euclideanMarginal f) := by
  rw [tensorizedGaussianCoupling, integral_map
    (measurable_tensorizedGaussianPair f hc hG hp).aemeasurable (by fun_prop)]
  simp_rw [tensorizedGaussianPair_cost]
  rw [integral_add (hI.comp_fst (gaussianReal 0 1)) hJ, integral_prod _ hJ,
    integral_prod _ (hI.comp_fst (gaussianReal 0 1))]
  simp only [integral_const, probReal_univ, one_smul]
  congr 1
  have hm := measurable_conditionalGaussianCost f hc hG hp
  rw [← integral_map measurable_fst.aemeasurable hm.aestronglyMeasurable, hfst]

theorem tensorizedGaussianCoupling_integrable_cost {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (π : Measure (E n × E n))
    (hfst : π.map Prod.fst = euclideanDensityLaw (euclideanMarginal f))
    (hsnd : π.map Prod.snd = stdGaussian (E n))
    (hsecond : Integrable (fun x : E (n+1) => ‖x‖^2) (euclideanDensityLaw f)) :
    Integrable (fun p => ‖p.1-p.2‖^2) (tensorizedGaussianCoupling f hc hG hp π) :=
  integrable_joint_quadratic_cost _ _ _
    (tensorizedGaussianCoupling_fst f hc hG hp π hfst)
    (tensorizedGaussianCoupling_snd f hc hG hp π hsnd)
    hsecond (integrable_norm_sq_stdGaussian (n+1))

theorem integrable_tensorizedConditionalCost {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (π : Measure (E n × E n))
    (hfst : π.map Prod.fst = euclideanDensityLaw (euclideanMarginal f))
    (hsnd : π.map Prod.snd = stdGaussian (E n))
    (hsecond : Integrable (fun x : E (n+1) => ‖x‖^2) (euclideanDensityLaw f)) :
    Integrable (fun p : (E n × E n) × ℝ =>
      (euclideanConditionalInverse f hc hG hp p.1.1 p.2-p.2)^2) (π.prod (gaussianReal 0 1)) := by
  have hcost := (tensorizedGaussianCoupling_integrable_cost f hc hG hp π hfst hsnd hsecond).comp_measurable
    (measurable_tensorizedGaussianPair f hc hG hp)
  have hm : Measurable (fun p : (E n × E n) × ℝ =>
      (euclideanConditionalInverse f hc hG hp p.1.1 p.2-p.2)^2) :=
    (((measurable_euclideanConditionalInverse f hc hG hp).comp
      (measurable_fst.prodMap measurable_id)).sub measurable_snd).pow_const 2
  apply hcost.mono' hm.aestronglyMeasurable
  filter_upwards with p
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), tensorizedGaussianPair_cost]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- Coupling-level cost tensorization with explicit scalar and entropy budgets.
Second moments establish joint-cost integrability independently of those budgets. -/
theorem tensorizedGaussianCoupling_cost_le {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (π : Measure (E n × E n)) [IsProbabilityMeasure π]
    (hfst : π.map Prod.fst = euclideanDensityLaw (euclideanMarginal f))
    (hsnd : π.map Prod.snd = stdGaussian (E n))
    (hsecond : Integrable (fun x : E (n+1) => ‖x‖^2) (euclideanDensityLaw f))
    (hI : Integrable (fun p : E n × E n => ‖p.1-p.2‖^2) π)
    (A D : ℝ) (K : E n → ℝ) (hK : Integrable K (euclideanDensityLaw (euclideanMarginal f)))
    (hA : (∫ p, ‖p.1-p.2‖^2 ∂π) ≤ 2*A)
    (hC : ∀ x, (∫ z, (euclideanConditionalInverse f hc hG hp x z-z)^2 ∂gaussianReal 0 1) ≤ 2*K x)
    (hchain : D = A + ∫ x, K x ∂euclideanDensityLaw (euclideanMarginal f)) :
    (∫ p, ‖p.1-p.2‖^2 ∂tensorizedGaussianCoupling f hc hG hp π) ≤ 2*D := by
  have hJ := integrable_tensorizedConditionalCost f hc hG hp π hfst hsnd hsecond
  have havg : Integrable (fun x : E n =>
      ∫ z, (euclideanConditionalInverse f hc hG hp x z-z)^2 ∂gaussianReal 0 1)
      (euclideanDensityLaw (euclideanMarginal f)) := by
    rw [← hfst]
    exact (integrable_map_measure
      (measurable_conditionalGaussianCost f hc hG hp).aestronglyMeasurable
      measurable_fst.aemeasurable).mpr hJ.integral_prod_left
  have hbound := integral_mono_ae havg (hK.const_mul 2) (ae_of_all _ hC)
  rw [integral_const_mul] at hbound
  rw [tensorizedGaussianCoupling_cost f hc hG hp π hfst hI hJ, hchain]
  linarith

#print axioms tensorizedGaussianCoupling_fst
#print axioms tensorizedGaussianCoupling_snd
#print axioms tensorizedGaussianCoupling_cost
#print axioms tensorizedGaussianCoupling_integrable_cost
#print axioms integrable_tensorizedConditionalCost
#print axioms tensorizedGaussianCoupling_cost_le
end CubeSections
