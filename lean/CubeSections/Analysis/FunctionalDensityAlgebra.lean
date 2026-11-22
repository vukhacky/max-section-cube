import CubeSections.Analysis.TransportIntegrand
import CubeSections.LinearAlgebra.WeightedGram

/-!
# Pointwise Gaussian algebra for functional Brascamp--Lieb

All rows of the actual isometric frame are retained, including zero rows.
The positive scalar values and arbitrary scores need not come from a CDF or a
transport. The determinant remainder and orthogonal residual give an exact
factorization, and hence the pointwise inequality used after change of variables.
-/
noncomputable section
open ProbabilityTheory
open scoped BigOperators
namespace CubeSections

theorem functionalGaussianSlope_pos {n : ℕ} (a t : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (i : Fin n) :
    0 < a i / gaussianPDFReal 0 1 (t i) :=
  div_pos (ha i) (gaussianPDFReal_pos 0 1 (t i) (by norm_num))

theorem functionalGaussian_det_pos {n k : ℕ} (U : Frame n k) (a t : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) :
    0 < (weightedGram (frameMatrix U) (fun i => a i / gaussianPDFReal 0 1 (t i))).det :=
  (frame_weightedGram_posDef U _ (functionalGaussianSlope_pos a t ha)).det_pos

theorem functionalGaussianSlope_log {n : ℕ} (a t : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (i : Fin n) :
    Real.log (a i / gaussianPDFReal 0 1 (t i)) =
      Real.log (a i) + Real.log (Real.sqrt (2*Real.pi)) + t i^2/2 := by
  rw [Real.log_div (ne_of_gt (ha i))
    (ne_of_gt (gaussianPDFReal_pos 0 1 (t i) (by norm_num))), log_standardGaussianPDF]
  ring

theorem functionalGaussianSlope_weighted_log {n k : ℕ} (U : Frame n k)
    (a t : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    (∑ i, leverage U i * Real.log (a i / gaussianPDFReal 0 1 (t i))) =
      (∑ i, leverage U i * Real.log (a i)) +
        (k : ℝ) * Real.log (Real.sqrt (2*Real.pi)) + ‖liftedScores U t‖^2/2 := by
  simp_rw [functionalGaussianSlope_log a t ha, mul_add, ← mul_div_assoc]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_leverage, ← Finset.sum_div, ← liftedScores_norm_sq]

theorem functionalGaussian_remainder_eq {n k : ℕ} (U : Frame n k)
    (a t : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    determinantRemainder U (fun i => Real.log (a i / gaussianPDFReal 0 1 (t i))) =
      Real.log ((weightedGram (frameMatrix U)
        (fun i => a i / gaussianPDFReal 0 1 (t i))).det) -
      ∑ i, leverage U i * Real.log (a i / gaussianPDFReal 0 1 (t i)) := by
  unfold determinantRemainder
  simp only [Real.exp_log (functionalGaussianSlope_pos a t ha _)]

/-- The exact logarithmic identity, before discarding either nonnegative defect. -/
theorem functionalGaussian_log_identity {n k : ℕ} (U : Frame n k)
    (a t : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    Real.log (euclideanGaussianDensity k (frameAdjoint U (liftedScores U t))) +
      Real.log ((weightedGram (frameMatrix U)
        (fun i => a i / gaussianPDFReal 0 1 (t i))).det) =
      (∑ i, leverage U i * Real.log (a i)) +
      determinantRemainder U (fun i => Real.log (a i / gaussianPDFReal 0 1 (t i))) +
      ‖frameResidual U (liftedScores U t)‖^2/2 := by
  rw [log_euclideanGaussianDensity, functionalGaussian_remainder_eq U a t ha,
    functionalGaussianSlope_weighted_log U a t ha, frame_residual_norm_sq]
  ring

theorem weightedFunctionProduct_eq_exp_sum {n k : ℕ} (U : Frame n k)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    (∏ i, (a i)^(leverage U i)) = Real.exp (∑ i, leverage U i * Real.log (a i)) := by
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.rpow_def_of_pos (ha i)]
  congr 1
  ring

/-- Positive weighted products equal Gaussian density times Jacobian after
removing the determinant and projection-residual defect factor. -/
theorem functionalGaussian_density_identity {n k : ℕ} (U : Frame n k)
    (a t : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    euclideanGaussianDensity k (frameAdjoint U (liftedScores U t)) *
      (weightedGram (frameMatrix U) (fun i => a i / gaussianPDFReal 0 1 (t i))).det =
      (∏ i, (a i)^(leverage U i)) *
      Real.exp (determinantRemainder U
        (fun i => Real.log (a i / gaussianPDFReal 0 1 (t i))) +
        ‖frameResidual U (liftedScores U t)‖^2/2) := by
  calc
    _ = Real.exp (Real.log (euclideanGaussianDensity k (frameAdjoint U (liftedScores U t))) +
        Real.log ((weightedGram (frameMatrix U)
          (fun i => a i / gaussianPDFReal 0 1 (t i))).det)) := by
      rw [Real.exp_add, Real.exp_log (euclideanGaussianDensity_pos _ _),
        Real.exp_log (functionalGaussian_det_pos U a t ha)]
    _ = Real.exp ((∑ i, leverage U i * Real.log (a i)) +
        determinantRemainder U (fun i => Real.log (a i / gaussianPDFReal 0 1 (t i))) +
        ‖frameResidual U (liftedScores U t)‖^2/2) :=
      congrArg Real.exp (functionalGaussian_log_identity U a t ha)
    _ = _ := by
      rw [weightedFunctionProduct_eq_exp_sum U a ha, ← Real.exp_add, add_assoc]

/-- The pointwise geometric functional BL inequality for arbitrary positive
scalar values and arbitrary real scores. No CDF, injectivity or integration
hypothesis occurs in this algebraic theorem. -/
theorem functionalGaussian_density_bound {n k : ℕ} (U : Frame n k)
    (a t : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    (∏ i, (a i)^(leverage U i)) ≤
      euclideanGaussianDensity k (frameAdjoint U (liftedScores U t)) *
      (weightedGram (frameMatrix U) (fun i => a i / gaussianPDFReal 0 1 (t i))).det := by
  rw [functionalGaussian_density_identity U a t ha]
  have hprod : 0 ≤ ∏ i, (a i)^(leverage U i) :=
    Finset.prod_nonneg (fun i _ => (Real.rpow_pos_of_pos (ha i) _).le)
  have hexp : 1 ≤ Real.exp (determinantRemainder U
      (fun i => Real.log (a i / gaussianPDFReal 0 1 (t i))) +
      ‖frameResidual U (liftedScores U t)‖^2/2) := by
    apply Real.one_le_exp_iff.mpr
    exact add_nonneg (determinantRemainder_nonneg U _) (div_nonneg (sq_nonneg _) (by norm_num))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hprod

#print axioms functionalGaussian_det_pos
#print axioms functionalGaussian_log_identity
#print axioms functionalGaussian_density_identity
#print axioms functionalGaussian_density_bound
end CubeSections
