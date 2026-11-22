import CubeSections.Analysis.PositiveGaussianLaw
import CubeSections.Analysis.GaussianDensity
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-! Actual probability, moments and entropy for Euclidean volume densities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal
namespace CubeSections

theorem euclideanDensityLaw_probability {n : ℕ} {f : E n → ℝ}
    (hi : Integrable f) (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) :
    IsProbabilityMeasure (euclideanDensityLaw f) := by
  constructor
  rw [euclideanDensityLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun x => (hp x).le)), hm]
  norm_num

theorem euclideanDensityLaw_integrable_iff {n : ℕ} {f : E n → ℝ}
    (hc : Continuous f) (hp : ∀ x, 0 < f x) (g : E n → ℝ) :
    Integrable g (euclideanDensityLaw f) ↔ Integrable (fun x => f x*g x) := by
  unfold euclideanDensityLaw
  simpa only [ENNReal.toReal_ofReal (hp _).le, smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' (g := g) hc.measurable.ennreal_ofReal
      (ae_of_all _ (fun x => ENNReal.ofReal_lt_top)))

theorem euclideanDensityLaw_integral {n : ℕ} {f : E n → ℝ}
    (hc : Continuous f) (hp : ∀ x, 0 < f x) (g : E n → ℝ) :
    (∫ x, g x ∂euclideanDensityLaw f) = ∫ x, f x*g x := by
  unfold euclideanDensityLaw
  rw [integral_withDensity_eq_integral_toReal_smul hc.measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hp _).le, smul_eq_mul]

def euclideanDensityGaussianRatio {n : ℕ} (f : E n → ℝ) (x : E n) : ℝ≥0∞ :=
  ENNReal.ofReal (f x) / ENNReal.ofReal (euclideanGaussianDensity n x)

theorem euclideanDensityLaw_eq_gaussian_withDensity {n : ℕ} {f : E n → ℝ}
    (hc : Continuous f) :
    euclideanDensityLaw f = (stdGaussian (E n)).withDensity (euclideanDensityGaussianRatio f) := by
  have hm : Measurable (euclideanDensityGaussianRatio f) :=
    hc.measurable.ennreal_ofReal.div (euclideanGaussianDensity_measurable n).ennreal_ofReal
  rw [stdGaussian_eq_euclideanGaussianDensity,
    ← withDensity_mul _ (euclideanGaussianDensity_measurable n).ennreal_ofReal hm]
  unfold euclideanDensityLaw
  congr 1
  funext x
  exact (ENNReal.mul_div_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr
    (euclideanGaussianDensity_pos n x))) ENNReal.ofReal_ne_top).symm

theorem euclideanDensityLaw_absolutelyContinuous {n : ℕ} {f : E n → ℝ}
    (hc : Continuous f) : euclideanDensityLaw f ≪ stdGaussian (E n) := by
  rw [euclideanDensityLaw_eq_gaussian_withDensity hc]
  exact withDensity_absolutelyContinuous _ _

theorem euclideanDensityLaw_llr {n : ℕ} {f : E n → ℝ}
    (hc : Continuous f) (hp : ∀ x, 0 < f x) :
    llr (euclideanDensityLaw f) (stdGaussian (E n)) =ᵐ[euclideanDensityLaw f]
      fun x => Real.log (f x / euclideanGaussianDensity n x) := by
  have hr : (euclideanDensityLaw f).rnDeriv (stdGaussian (E n)) =ᵐ[stdGaussian (E n)]
      euclideanDensityGaussianRatio f := by
    rw [euclideanDensityLaw_eq_gaussian_withDensity hc]
    exact Measure.rnDeriv_withDensity _
      (hc.measurable.ennreal_ofReal.div (euclideanGaussianDensity_measurable n).ennreal_ofReal)
  filter_upwards [(euclideanDensityLaw_absolutelyContinuous hc).ae_le hr] with x hx
  rw [llr, hx, euclideanDensityGaussianRatio, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (hp x).le,
    ENNReal.toReal_ofReal (euclideanGaussianDensity_pos n x).le]

theorem euclideanDensityLaw_memLp_two {n : ℕ} {f : E n → ℝ}
    (hc : Continuous f) (hp : ∀ x, 0 < f x)
    (hi : Integrable (fun x => ‖x‖^2*f x)) :
    MemLp id 2 (euclideanDensityLaw f) := by
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
  apply (euclideanDensityLaw_integrable_iff hc hp _).mpr
  simpa only [id_eq, mul_comm] using hi

theorem euclideanDensityLaw_entropy_integrable {n : ℕ} {f : E n → ℝ}
    (hc : Continuous f) (hp : ∀ x, 0 < f x) (hi : Integrable f)
    (hm : (∫ x, f x) = 1)
    (hlog : Integrable (fun x => f x*Real.log (f x)))
    (hsecond : Integrable (fun x => ‖x‖^2*f x)) :
    Integrable (llr (euclideanDensityLaw f) (stdGaussian (E n))) (euclideanDensityLaw f) := by
  letI := euclideanDensityLaw_probability hi hp hm
  have hL : Integrable (fun x => Real.log (f x)) (euclideanDensityLaw f) :=
    (euclideanDensityLaw_integrable_iff hc hp _).mpr hlog
  have hS : Integrable (fun x => ‖x‖^2) (euclideanDensityLaw f) :=
    (euclideanDensityLaw_integrable_iff hc hp _).mpr (by simpa only [mul_comm] using hsecond)
  have hG : Integrable (fun x => Real.log (euclideanGaussianDensity n x)) (euclideanDensityLaw f) := by
    simp_rw [log_euclideanGaussianDensity]
    exact (integrable_const _).sub (hS.div_const 2)
  apply ((hL.sub hG).congr ?_).congr (euclideanDensityLaw_llr hc hp).symm
  exact ae_of_all _ (fun x => (Real.log_div (ne_of_gt (hp x))
    (ne_of_gt (euclideanGaussianDensity_pos n x))).symm)

theorem euclideanDensityLaw_klDiv_eq_integral {n : ℕ} {f : E n → ℝ}
    (hc : Continuous f) (hp : ∀ x, 0 < f x) (hi : Integrable f)
    (hm : (∫ x, f x) = 1) :
    (klDiv (euclideanDensityLaw f) (stdGaussian (E n))).toReal =
      ∫ x, f x*Real.log (f x / euclideanGaussianDensity n x) := by
  letI := euclideanDensityLaw_probability hi hp hm
  rw [toReal_klDiv_of_measure_eq (euclideanDensityLaw_absolutelyContinuous hc) (by simp),
    integral_congr_ae (euclideanDensityLaw_llr hc hp), euclideanDensityLaw_integral hc hp]

#print axioms euclideanDensityLaw_entropy_integrable
#print axioms euclideanDensityLaw_klDiv_eq_integral
end CubeSections
