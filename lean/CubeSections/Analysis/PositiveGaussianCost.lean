import CubeSections.Analysis.ConditionalDensityLaw
import CubeSections.Analysis.EuclideanGaussianSplit
import CubeSections.Analysis.TransportCoupling

/-! Actual triangular couplings for positive Gaussian-dominated densities.
The probabilistic construction is unconditional once the lower-dimensional
transport law is provided. Cost budgets are explicit hypotheses of the
intermediate tensorization theorem, not hidden claims of Gaussian T2. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CubeSections

def triangularGaussianMap {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (T : E n → E n) (p : E n × ℝ) : E (n+1) :=
  euclideanSuccJoin n (T p.1, euclideanConditionalInverse f hc hG hp (T p.1) p.2)

theorem measurable_triangularGaussianMap {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (T : E n → E n) (hT : Measurable T) : Measurable (triangularGaussianMap f hc hG hp T) :=
  (continuous_euclideanSuccJoin n).measurable.comp
    ((measurable_triangularConditionalInverse f hc hG hp).comp (hT.prodMap measurable_id))

theorem triangularGaussianMap_law {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (T : E n → E n) (hT : Measurable T)
    (hLaw : (stdGaussian (E n)).map T = euclideanDensityLaw (euclideanMarginal f)) :
    ((stdGaussian (E n)).prod (gaussianReal 0 1)).map (triangularGaussianMap f hc hG hp T) =
      euclideanDensityLaw f := by
  have hprod : ((stdGaussian (E n)).prod (gaussianReal 0 1)).map (Prod.map T id) =
      (euclideanDensityLaw (euclideanMarginal f)).prod (gaussianReal 0 1) := by
    rw [← Measure.map_prod_map _ _ hT measurable_id, Measure.map_id, hLaw]
  have hcomp : triangularGaussianMap f hc hG hp T =
      euclideanSuccJoin n ∘ triangularConditionalInverse f hc hG hp ∘ Prod.map T id := rfl
  rw [hcomp, ← Measure.map_map (continuous_euclideanSuccJoin n).measurable
    ((measurable_triangularConditionalInverse f hc hG hp).comp (hT.prodMap measurable_id)),
    ← Measure.map_map (measurable_triangularConditionalInverse f hc hG hp) (hT.prodMap measurable_id),
    hprod, euclideanDensityLaw, triangularConditionalInverse_map_law,
    euclideanSuccJoin_density_map f hc.measurable]

def triangularGaussianCoupling {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (T : E n → E n) : Measure (E (n+1) × E (n+1)) :=
  ((stdGaussian (E n)).prod (gaussianReal 0 1)).map
    (fun p => (triangularGaussianMap f hc hG hp T p, euclideanSuccJoin n p))

theorem triangularGaussianCoupling_probability {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (T : E n → E n) (hT : Measurable T) :
    IsProbabilityMeasure (triangularGaussianCoupling f hc hG hp T) := by
  have hpair := (measurable_triangularGaussianMap f hc hG hp T hT).prodMk
    (continuous_euclideanSuccJoin n).measurable
  constructor
  rw [triangularGaussianCoupling, Measure.map_apply hpair MeasurableSet.univ,
    Set.preimage_univ, measure_univ]

theorem triangularGaussianCoupling_fst {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (T : E n → E n) (hT : Measurable T)
    (hLaw : (stdGaussian (E n)).map T = euclideanDensityLaw (euclideanMarginal f)) :
    (triangularGaussianCoupling f hc hG hp T).map Prod.fst = euclideanDensityLaw f := by
  rw [triangularGaussianCoupling, Measure.map_map measurable_fst
    ((measurable_triangularGaussianMap f hc hG hp T hT).prodMk
      (continuous_euclideanSuccJoin n).measurable)]
  exact triangularGaussianMap_law f hc hG hp T hT hLaw

theorem triangularGaussianCoupling_snd {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (T : E n → E n) (hT : Measurable T) :
    (triangularGaussianCoupling f hc hG hp T).map Prod.snd = stdGaussian (E (n+1)) := by
  rw [triangularGaussianCoupling, Measure.map_map measurable_snd
    ((measurable_triangularGaussianMap f hc hG hp T hT).prodMk
      (continuous_euclideanSuccJoin n).measurable)]
  exact euclideanSuccJoin_gaussian_map n

theorem triangularGaussianMap_cost_pointwise {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (T : E n → E n) (p : E n × ℝ) :
    ‖triangularGaussianMap f hc hG hp T p - euclideanSuccJoin n p‖^2 =
      ‖T p.1-p.1‖^2 + (euclideanConditionalInverse f hc hG hp (T p.1) p.2-p.2)^2 :=
  euclideanSuccJoin_sub_norm_sq n (T p.1) p.1 _ p.2

theorem triangularGaussianCoupling_cost {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (T : E n → E n) (hT : Measurable T)
    (hI : Integrable (fun x : E n => ‖T x-x‖^2) (stdGaussian (E n)))
    (hJ : Integrable (fun p : E n × ℝ =>
      (euclideanConditionalInverse f hc hG hp (T p.1) p.2-p.2)^2)
      ((stdGaussian (E n)).prod (gaussianReal 0 1))) :
    (∫ p, ‖p.1-p.2‖^2 ∂triangularGaussianCoupling f hc hG hp T) =
      (∫ x, ‖T x-x‖^2 ∂stdGaussian (E n)) +
      ∫ x, ∫ z, (euclideanConditionalInverse f hc hG hp (T x) z-z)^2
        ∂gaussianReal 0 1 ∂stdGaussian (E n) := by
  rw [triangularGaussianCoupling, integral_map
    ((measurable_triangularGaussianMap f hc hG hp T hT).prodMk
      (continuous_euclideanSuccJoin n).measurable).aemeasurable (by fun_prop)]
  simp_rw [triangularGaussianMap_cost_pointwise]
  rw [integral_add (hI.comp_fst (gaussianReal 0 1)) hJ, integral_prod _ hJ,
    integral_prod _ (hI.comp_fst (gaussianReal 0 1))]
  simp

/-- The tensorized coupling has the sum of the marginal cost budget and the
averaged conditional cost budget. -/
theorem triangularGaussianCoupling_cost_le {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x)
    (T : E n → E n) (hT : Measurable T)
    (hI : Integrable (fun x : E n => ‖T x-x‖^2) (stdGaussian (E n)))
    (hJ : Integrable (fun p : E n × ℝ =>
      (euclideanConditionalInverse f hc hG hp (T p.1) p.2-p.2)^2)
      ((stdGaussian (E n)).prod (gaussianReal 0 1)))
    (A B : ℝ) (hA : (∫ x, ‖T x-x‖^2 ∂stdGaussian (E n)) ≤ 2*A)
    (hB : (∫ x, ∫ z, (euclideanConditionalInverse f hc hG hp (T x) z-z)^2
      ∂gaussianReal 0 1 ∂stdGaussian (E n)) ≤ 2*B) :
    (∫ p, ‖p.1-p.2‖^2 ∂triangularGaussianCoupling f hc hG hp T) ≤ 2*(A+B) := by
  rw [triangularGaussianCoupling_cost f hc hG hp T hT hI hJ]
  linarith

#print axioms triangularGaussianMap_law
#print axioms triangularGaussianCoupling_probability
#print axioms triangularGaussianCoupling_fst
#print axioms triangularGaussianCoupling_snd
#print axioms triangularGaussianCoupling_cost
#print axioms triangularGaussianCoupling_cost_le
end CubeSections
