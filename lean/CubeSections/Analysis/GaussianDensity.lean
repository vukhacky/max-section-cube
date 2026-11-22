import CubeSections.Semantics
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The actual standard Gaussian density on the Euclidean parameter space. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace CubeSections

def euclideanGaussianDensity (k : ℕ) (x : E k) : ℝ :=
  ∏ i, gaussianPDFReal 0 1 (x i)

theorem euclideanGaussianDensity_pos (k : ℕ) (x : E k) :
    0 < euclideanGaussianDensity k x := by
  exact Finset.prod_pos (fun i _ => gaussianPDFReal_pos 0 1 (x i) (by norm_num))

theorem euclideanGaussianDensity_measurable (k : ℕ) :
    Measurable (euclideanGaussianDensity k) := by
  unfold euclideanGaussianDensity
  fun_prop

theorem euclideanGaussianDensity_integrable (k : ℕ) :
    Integrable (euclideanGaussianDensity k) := by
  have hi : Integrable (fun x : Fin k → ℝ => ∏ i, gaussianPDFReal 0 1 (x i)) :=
    Integrable.fintype_prod (μ := fun _ : Fin k => (volume : Measure ℝ))
      (f := fun _ : Fin k => gaussianPDFReal 0 1) (fun _ => integrable_gaussianPDFReal 0 1)
  exact ((PiLp.volume_preserving_toLp (Fin k)).integrable_comp_emb
    (g := euclideanGaussianDensity k)
    (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurableEmbedding).1 hi

theorem euclideanGaussianDensity_integral (k : ℕ) :
    ∫ x, euclideanGaussianDensity k x = 1 := by
  rw [← (PiLp.volume_preserving_toLp (Fin k)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurableEmbedding (euclideanGaussianDensity k)]
  change (∫ x : Fin k → ℝ, ∏ i, gaussianPDFReal 0 1 (x i)) = 1
  rw [integral_fintype_prod_volume_eq_prod]
  apply Finset.prod_eq_one
  intro i hi
  exact integral_gaussianPDFReal_eq_one 0 (by norm_num : (1 : NNReal) ≠ 0)

theorem log_standardGaussianPDF (t : ℝ) :
    Real.log (gaussianPDFReal 0 1 t) = -Real.log (Real.sqrt (2 * Real.pi)) - t ^ 2 / 2 := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
  ring

theorem log_euclideanGaussianDensity (k : ℕ) (x : E k) :
    Real.log (euclideanGaussianDensity k x) =
      -(k : ℝ) * Real.log (Real.sqrt (2 * Real.pi)) - ‖x‖ ^ 2 / 2 := by
  rw [euclideanGaussianDensity, Real.log_prod
    (fun i _ => ne_of_gt (gaussianPDFReal_pos 0 1 (x i) (by norm_num)))]
  simp_rw [log_standardGaussianPDF]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_div, EuclideanSpace.real_norm_sq_eq]
  ring

theorem pi_standardGaussian_withDensity (k : ℕ) :
    (Measure.pi fun _ : Fin k => gaussianReal 0 1) =
      (volume : Measure (Fin k → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hi : Integrable (fun x : Fin k → ℝ => ∏ i, gaussianPDFReal 0 1 (x i)) :=
    Integrable.fintype_prod (μ := fun _ : Fin k => (volume : Measure ℝ))
      (f := fun _ : Fin k => gaussianPDFReal 0 1) (fun _ => integrable_gaussianPDFReal 0 1)
  rw [← ofReal_integral_eq_lintegral_ofReal hi.restrict
    (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 (x i))))]
  change ENNReal.ofReal (∫ x, ∏ i, gaussianPDFReal 0 1 (x i)
    ∂(Measure.pi fun _ : Fin k => (volume : Measure ℝ)).restrict (Set.pi Set.univ s)) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (gaussianPDFReal_nonneg 0 1))]
  congr 1
  funext i
  exact (gaussianReal_apply_eq_integral 0 (by norm_num) (s i)).symm

theorem stdGaussian_eq_euclideanGaussianDensity (k : ℕ) :
    stdGaussian (E k) = (volume : Measure (E k)).withDensity
      (fun x => ENNReal.ofReal (euclideanGaussianDensity k x)) := by
  rw [← map_pi_eq_stdGaussian, pi_standardGaussian_withDensity]
  ext s hs
  rw [Measure.map_apply (PiLp.volume_preserving_toLp (Fin k)).measurable hs,
    withDensity_apply _ ((PiLp.volume_preserving_toLp (Fin k)).measurable hs),
    withDensity_apply _ hs]
  exact (PiLp.volume_preserving_toLp (Fin k)).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurableEmbedding
    (fun x : E k => ENNReal.ofReal (euclideanGaussianDensity k x)) s

end CubeSections
