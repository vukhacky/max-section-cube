import CubeSections.Analysis.CompactGaussianMap
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! One-dimensional Gaussian quadratic transport for actual compactly supported
C1 increasing perturbations. This does not assert the general Talagrand theorem. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory InformationTheory
open scoped ContDiff NNReal ENNReal

namespace CubeSections.CompactGaussianPerturbation

variable (d : CompactGaussianPerturbation)

theorem compactSupport_log_slope : HasCompactSupport (fun x => Real.log (d.slope x)) := by
  exact d.compactSupport.deriv.comp_left (g := fun t : ℝ => Real.log (1 + t)) (by simp)

theorem continuous_log_slope : Continuous (fun x => Real.log (d.slope x)) :=
  d.continuous_slope.log (fun x => ne_of_gt (d.positive_slope x))

theorem integrable_log_slope : Integrable (fun x => Real.log (d.slope x)) (gaussianReal 0 1) :=
  d.continuous_log_slope.integrable_of_hasCompactSupport d.compactSupport_log_slope

theorem integrable_displacement_sq : Integrable (fun x => d.displacement x ^ 2) (gaussianReal 0 1) := by
  have hc : Continuous (fun x => d.displacement x ^ 2) := d.contDiff.continuous.pow 2
  apply hc.integrable_of_hasCompactSupport
  exact d.compactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)

theorem integrable_map_sq : Integrable (fun x => d.map x ^ 2) (gaussianReal 0 1) := by
  have hI := ((memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq.add
    ((integrable_gaussian_compact_mul_id d.contDiff.continuous d.compactSupport).const_mul 2)).add
    d.integrable_displacement_sq
  apply hI.congr
  filter_upwards with x
  simp only [Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply, id_eq, map]
  ring

theorem memLp_id_law_two : MemLp id 2 d.law := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  exact (integrable_map_measure (by fun_prop) d.measurable_map.aemeasurable).mpr d.integrable_map_sq

def entropyIntegrand (x : ℝ) : ℝ :=
  x * d.displacement x + d.displacement x ^ 2 / 2 - Real.log (d.slope x)

theorem integrable_entropyIntegrand : Integrable d.entropyIntegrand (gaussianReal 0 1) :=
  ((integrable_gaussian_compact_mul_id d.contDiff.continuous d.compactSupport).add
    (d.integrable_displacement_sq.div_const 2)).sub d.integrable_log_slope

theorem log_gaussianDensity_map_eq_entropyIntegrand (x : ℝ) :
    Real.log (d.gaussianDensity (d.map x)).toReal = d.entropyIntegrand x := by
  rw [d.log_gaussianDensity_map]
  unfold map entropyIntegrand
  ring

theorem llr_map :
    (fun x => llr d.law (gaussianReal 0 1) (d.map x)) =ᵐ[gaussianReal 0 1] d.entropyIntegrand := by
  have hν := d.absolutelyContinuous_gaussian.ae_le d.rnDeriv_law
  have hsrc := ae_of_ae_map d.measurable_map.aemeasurable hν
  filter_upwards [hsrc] with x hx
  rw [llr, hx]
  exact d.log_gaussianDensity_map_eq_entropyIntegrand x

theorem integrable_llr : Integrable (llr d.law (gaussianReal 0 1)) d.law := by
  have hc : Integrable (fun x => llr d.law (gaussianReal 0 1) (d.map x)) (gaussianReal 0 1) :=
    d.integrable_entropyIntegrand.congr d.llr_map.symm
  exact (integrable_map_measure (measurable_llr _ _).aestronglyMeasurable
    d.measurable_map.aemeasurable).mpr hc

theorem klDiv_finite : klDiv d.law (gaussianReal 0 1) ≠ (⊤ : ℝ≥0∞) :=
  klDiv_ne_top d.absolutelyContinuous_gaussian d.integrable_llr

def derivativeProduction (x : ℝ) : ℝ := deriv d.displacement x - Real.log (d.slope x)

theorem derivativeProduction_nonneg (x : ℝ) : 0 ≤ d.derivativeProduction x := by
  have hlog := Real.log_le_sub_one_of_pos (d.positive_slope x)
  change 0 ≤ deriv d.displacement x - Real.log (d.slope x)
  dsimp only [slope] at hlog ⊢
  linarith

theorem integrable_derivativeProduction : Integrable d.derivativeProduction (gaussianReal 0 1) :=
  (integrable_gaussian_compact_deriv d.contDiff d.compactSupport).sub d.integrable_log_slope

/-- The actual KL identity, including the nonnegative one-dimensional derivative
production. All densities and integrability statements have been proved above. -/
theorem klDiv_decomposition :
    (klDiv d.law (gaussianReal 0 1)).toReal =
      (1 / 2 : ℝ) * (∫ x, d.displacement x ^ 2 ∂gaussianReal 0 1) +
      ∫ x, d.derivativeProduction x ∂gaussianReal 0 1 := by
  rw [toReal_klDiv_of_measure_eq d.absolutelyContinuous_gaussian (by simp)]
  rw [law, integral_map d.measurable_map.aemeasurable (measurable_llr _ _).aestronglyMeasurable]
  change (∫ x, llr d.law (gaussianReal 0 1) (d.map x) ∂gaussianReal 0 1) = _
  rw [integral_congr_ae d.llr_map]
  change (∫ x, (x * d.displacement x + d.displacement x ^ 2 / 2) - Real.log (d.slope x)
    ∂gaussianReal 0 1) = _
  have hsum : Integrable (fun x => x * d.displacement x + d.displacement x ^ 2 / 2)
      (gaussianReal 0 1) :=
    (integrable_gaussian_compact_mul_id d.contDiff.continuous d.compactSupport).add
      (d.integrable_displacement_sq.div_const 2)
  rw [integral_sub hsum d.integrable_log_slope,
    integral_add (integrable_gaussian_compact_mul_id d.contDiff.continuous d.compactSupport)
      (d.integrable_displacement_sq.div_const 2), integral_div]
  change _ = (1 / 2 : ℝ) * (∫ x, d.displacement x ^ 2 ∂gaussianReal 0 1) +
    ∫ x, deriv d.displacement x - Real.log (d.slope x) ∂gaussianReal 0 1
  rw [integral_sub (integrable_gaussian_compact_deriv d.contDiff d.compactSupport) d.integrable_log_slope,
    gaussian_stein_compact d.contDiff d.compactSupport]
  ring

theorem displacement_cost_le_twice_klDiv :
    (∫ x, d.displacement x ^ 2 ∂gaussianReal 0 1) ≤ 2 * (klDiv d.law (gaussianReal 0 1)).toReal := by
  rw [d.klDiv_decomposition]
  have hp := integral_nonneg d.derivativeProduction_nonneg (μ := gaussianReal 0 1)
  linarith

/-- The explicit graph coupling `(g(Z),Z)` for `Z` standard Gaussian. -/
def coupling : Measure (ℝ × ℝ) := (gaussianReal 0 1).map (fun x => (d.map x, x))

instance coupling_probability : IsProbabilityMeasure d.coupling := by unfold coupling; infer_instance

theorem coupling_fst : d.coupling.map Prod.fst = d.law := by
  rw [coupling, Measure.map_map measurable_fst (by fun_prop)]
  rfl

theorem coupling_snd : d.coupling.map Prod.snd = gaussianReal 0 1 := by
  rw [coupling, Measure.map_map measurable_snd (by fun_prop)]
  exact Measure.map_id

theorem coupling_cost_integrable : Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ 2) d.coupling := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  apply d.integrable_displacement_sq.congr
  filter_upwards with x
  simp [map, sq_abs]

theorem coupling_cost :
    (∫ p : ℝ × ℝ, |p.1 - p.2| ^ 2 ∂d.coupling) = ∫ x, d.displacement x ^ 2 ∂gaussianReal 0 1 := by
  rw [coupling, integral_map (by fun_prop) (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with x
  simp [map, sq_abs]

/-- The genuine one-dimensional Gaussian transport inequality for this explicit
smooth compact perturbation class, witnessed by its actual graph coupling. -/
theorem quadratic_transport :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      π.map Prod.fst = d.law ∧ π.map Prod.snd = gaussianReal 0 1 ∧
      Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ 2) π ∧
      (∫ p : ℝ × ℝ, |p.1 - p.2| ^ 2 ∂π) ≤ 2 * (klDiv d.law (gaussianReal 0 1)).toReal := by
  refine ⟨d.coupling, inferInstance, d.coupling_fst, d.coupling_snd, d.coupling_cost_integrable, ?_⟩
  rw [d.coupling_cost]
  exact d.displacement_cost_le_twice_klDiv

end CubeSections.CompactGaussianPerturbation

namespace CubeSections

/-- Unbundled form: an actual C1 compact perturbation with positive derivative
has a graph coupling whose quadratic cost is at most twice its actual KL. -/
theorem gaussian_quadratic_transport_compact (h : ℝ → ℝ)
    (hc : ContDiff ℝ 1 h) (hs : HasCompactSupport h) (hp : ∀ x, 0 < 1 + deriv h x) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      π.map Prod.fst = (gaussianReal 0 1).map (fun x => x + h x) ∧
      π.map Prod.snd = gaussianReal 0 1 ∧
      Integrable (fun p : ℝ × ℝ => |p.1 - p.2| ^ 2) π ∧
      (∫ p : ℝ × ℝ, |p.1 - p.2| ^ 2 ∂π) ≤
        2 * (klDiv ((gaussianReal 0 1).map (fun x => x + h x)) (gaussianReal 0 1)).toReal :=
  (CompactGaussianPerturbation.mk h hc hs hp).quadratic_transport

end CubeSections
