import CubeSections.Analysis.ConditionalDensityEntropy
import CubeSections.Analysis.GaussianDensityEntropy
import CubeSections.Analysis.EuclideanDensityLaw
import CubeSections.Analysis.PositiveDensityEntropy

/-! Actual finite Gaussian relative entropies and their conditional chain rule
for continuous positive Gaussian-dominated densities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace CubeSections

theorem GaussianDominated.memLp_two {n : ℕ} {f : E n → ℝ}
    (hG : GaussianDominated f) (hc : Continuous f) (hp : ∀ x, 0 < f x) :
    MemLp id 2 (euclideanDensityLaw f) :=
  euclideanDensityLaw_memLp_two hc hp
    (hG.norm_sq_mul.integrable ((continuous_norm.pow 2).mul hc))

theorem GaussianDominated.integrable_secondMoment {n : ℕ} {f : E n → ℝ}
    (hG : GaussianDominated f) (hc : Continuous f) (hp : ∀ x, 0 < f x) :
    Integrable (fun x : E n => ‖x‖^2) (euclideanDensityLaw f) :=
  (memLp_two_iff_integrable_sq_norm (by fun_prop)).mp (hG.memLp_two hc hp)

theorem GaussianDominated.klDiv_ne_top {n : ℕ} {f : E n → ℝ}
    (hG : GaussianDominated f) (hc : Continuous f) (hp : ∀ x, 0 < f x)
    (hm : (∫ x, f x)=1) : klDiv (euclideanDensityLaw f) (stdGaussian (E n)) ≠ ⊤ :=
  InformationTheory.klDiv_ne_top (euclideanDensityLaw_absolutelyContinuous hc)
    (euclideanDensityLaw_entropy_integrable hc hp (hG.integrable hc) hm
      (hG.integrable_mul_log hc hp) (hG.norm_sq_mul.integrable ((continuous_norm.pow 2).mul hc)))

theorem GaussianDominated.integrable_logRatio {n : ℕ} {f : E n → ℝ}
    (hG : GaussianDominated f) (hc : Continuous f) (hp : ∀ x, 0 < f x)
    (hm : (∫ x, f x)=1) :
    Integrable (fun x => f x*Real.log (f x/euclideanGaussianDensity n x)) := by
  have h := ((klDiv_ne_top_iff.mp (hG.klDiv_ne_top hc hp hm)).2).congr
    (euclideanDensityLaw_llr hc hp)
  exact (euclideanDensityLaw_integrable_iff hc hp _).mp h

def euclideanConditionalKL {n : ℕ} (f : E (n+1) → ℝ) (x : E n) : ℝ :=
  (klDiv (positiveDensityLaw (euclideanConditionalDensity f x)) (gaussianReal 0 1)).toReal

theorem euclideanConditionalKL_eq_integral {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x) (x : E n) :
    euclideanConditionalKL f x = ∫ s, euclideanConditionalDensity f x s *
      Real.log (euclideanConditionalDensity f x s / gaussianPDFReal 0 1 s) :=
  positiveDensity_klDiv_eq_densityIntegral (continuous_euclideanConditionalSlice f hc x)
    (integrable_euclideanConditionalSlice f hc hG x)
    (euclideanConditionalDensity_pos f hc hG hp x)
    (integral_euclideanConditionalDensity f hc hG hp x)

theorem euclideanConditionalKL_chain {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x) (hm : (∫ x, f x)=1) :
    (klDiv (euclideanDensityLaw f) (stdGaussian (E (n+1)))).toReal =
      (klDiv (euclideanDensityLaw (euclideanMarginal f)) (stdGaussian (E n))).toReal +
      ∫ x, euclideanConditionalKL f x ∂euclideanDensityLaw (euclideanMarginal f) := by
  have hMc := continuous_euclideanMarginal f hc hG
  have hMG := gaussianDominated_euclideanMarginal f hc hG
  have hMp := euclideanMarginal_pos f hc hG hp
  have hMm : (∫ x, euclideanMarginal f x)=1 := (integral_euclideanMarginal f hc hG).trans hm
  rw [euclideanDensityLaw_klDiv_eq_integral hc hp (hG.integrable hc) hm,
    euclideanDensityLaw_klDiv_eq_integral hMc hMp (hMG.integrable hMc) hMm,
    euclideanDensityLaw_integral hMc hMp]
  simp_rw [euclideanConditionalKL_eq_integral f hc hG hp]
  exact euclideanConditionalDensity_entropy_chain f hc hG hp
    (hG.integrable_logRatio hc hp hm) (hMG.integrable_logRatio hMc hMp hMm)

theorem integrable_euclideanConditionalKL {n : ℕ} (f : E (n+1) → ℝ)
    (hc : Continuous f) (hG : GaussianDominated f) (hp : ∀ x, 0 < f x) (hm : (∫ x, f x)=1) :
    Integrable (euclideanConditionalKL f) (euclideanDensityLaw (euclideanMarginal f)) := by
  have hMc := continuous_euclideanMarginal f hc hG
  have hMG := gaussianDominated_euclideanMarginal f hc hG
  have hMp := euclideanMarginal_pos f hc hG hp
  have hMm : (∫ x, euclideanMarginal f x)=1 := (integral_euclideanMarginal f hc hG).trans hm
  have hF := euclideanSuccJoin_integrable
    (fun x : E (n+1) => f x * Real.log (f x / euclideanGaussianDensity (n+1) x))
    (hG.integrable_logRatio hc hp hm)
  have hM := integrable_joint_marginalEntropy f hc hG hp
    (hMG.integrable_logRatio hMc hMp hMm)
  have hC : Integrable (fun p : E n × ℝ => f (euclideanSuccJoin n p) *
      Real.log (euclideanConditionalDensity f p.1 p.2 / gaussianPDFReal 0 1 p.2))
      ((volume : Measure (E n)).prod volume) := by
    apply (hF.sub hM).congr
    filter_upwards with p
    simp only [Pi.sub_apply]
    rw [euclideanConditionalDensity_log_split f hc hG hp p.1 p.2]
    ring
  apply (euclideanDensityLaw_integrable_iff hMc hMp _).mpr
  apply hC.integral_prod_left.congr
  filter_upwards with x
  rw [euclideanConditionalKL_eq_integral f hc hG hp x, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  unfold euclideanConditionalDensity
  field_simp [ne_of_gt (hMp x)]

#print axioms GaussianDominated.klDiv_ne_top
#print axioms euclideanConditionalKL_chain
#print axioms integrable_euclideanConditionalKL
end CubeSections
