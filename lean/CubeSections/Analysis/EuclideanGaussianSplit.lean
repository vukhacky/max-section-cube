import CubeSections.Analysis.EuclideanSplit
import CubeSections.Analysis.GaussianDensity
import CubeSections.Analysis.PositiveGaussianLaw
import CubeSections.Analysis.TransportDensity

/-! Exact Gaussian and Lebesgue density laws under the Euclidean coordinate split. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CubeSections

theorem euclideanGaussianDensity_succ_join (n : ℕ) (x : E n) (s : ℝ) :
    euclideanGaussianDensity (n+1) (euclideanSuccJoin n (x,s)) =
      euclideanGaussianDensity n x * gaussianPDFReal 0 1 s := by
  simp only [euclideanGaussianDensity, Fin.prod_univ_succ,
    euclideanSuccJoin_zero, euclideanSuccJoin_succ]
  exact mul_comm _ _

theorem euclideanSuccJoin_density_map {n : ℕ} (f : E (n+1) → ℝ)
    (hf : Measurable f) :
    (((volume : Measure (E n)).prod volume).withDensity
      (fun p => ENNReal.ofReal (f (euclideanSuccJoin n p)))).map (euclideanSuccJoin n) =
      euclideanDensityLaw f := by
  have h := map_withDensity_comp_eq ((volume : Measure (E n)).prod volume)
    (euclideanSuccJoin n) (continuous_euclideanSuccJoin n).measurable
    (fun x => ENNReal.ofReal (f x)) hf.ennreal_ofReal
  rw [(euclideanSuccJoin_measurePreserving n).map_eq] at h
  exact h

theorem euclideanSuccJoin_gaussian_map (n : ℕ) :
    ((stdGaussian (E n)).prod (gaussianReal 0 1)).map (euclideanSuccJoin n) =
      stdGaussian (E (n+1)) := by
  rw [stdGaussian_eq_euclideanGaussianDensity n,
    gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : NNReal) ≠ 0),
    prod_withDensity (euclideanGaussianDensity_measurable n).ennreal_ofReal (measurable_gaussianPDF 0 1)]
  have heq : (fun p : E n × ℝ => ENNReal.ofReal (euclideanGaussianDensity n p.1) * gaussianPDF 0 1 p.2) =
      fun p => ENNReal.ofReal (euclideanGaussianDensity (n+1) (euclideanSuccJoin n p)) := by
    funext p
    rw [euclideanGaussianDensity_succ_join, gaussianPDF_def,
      ENNReal.ofReal_mul (euclideanGaussianDensity_pos n p.1).le]
  rw [heq, euclideanSuccJoin_density_map _ (euclideanGaussianDensity_measurable (n+1)),
    euclideanDensityLaw, ← stdGaussian_eq_euclideanGaussianDensity]

theorem euclideanSuccJoin_sub_norm_sq (n : ℕ) (x y : E n) (s t : ℝ) :
    ‖euclideanSuccJoin n (x,s) - euclideanSuccJoin n (y,t)‖^2 =
      ‖x-y‖^2 + (s-t)^2 := by
  rw [← map_sub]
  exact euclideanSuccJoin_norm_sq n (x-y) (s-t)

#print axioms euclideanSuccJoin_gaussian_map
#print axioms euclideanSuccJoin_density_map
end CubeSections
