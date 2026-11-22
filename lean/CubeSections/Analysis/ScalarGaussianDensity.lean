import CubeSections.Analysis.PositiveDensityEntropy
import CubeSections.Analysis.GaussianDensityEntropy

/-! Scalar finite-moment and entropy consequences of a Gaussian bound.
The volume-preserving one-dimensional Euclidean coordinate isometry transfers
the multidimensional Gaussian estimates to real densities. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
namespace CubeSections

private def scalarLineCoordinateIsometry : E 1 ≃ₗᵢ[ℝ] ℝ where
  toFun x := x 0
  invFun t := WithLp.toLp 2 (fun _ : Fin 1 => t)
  left_inv x := by
    ext i
    simp only [Subsingleton.elim i (0 : Fin 1)]
  right_inv t := rfl
  map_add' x y := rfl
  map_smul' a x := rfl
  norm_map' x := by
    change ‖x 0‖ = ‖x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_one, Real.norm_eq_abs, sq_abs]

private theorem lineCoordinateIsometry_sq (x : E 1) : (scalarLineCoordinateIsometry x)^2 = ‖x‖^2 := by
  rw [← sq_abs, ← Real.norm_eq_abs, scalarLineCoordinateIsometry.norm_map]

private theorem scalarGaussianBound_lift {f : ℝ → ℝ} (C a : ℝ) (hC : 0 < C) (ha : 0 < a)
    (hbound : ∀ s, |f s| ≤ C*Real.exp (-a*s^2)) :
    GaussianDominated (fun x : E 1 => f (scalarLineCoordinateIsometry x)) := by
  refine ⟨C,a,hC,ha,fun x => ?_⟩
  simpa only [lineCoordinateIsometry_sq] using hbound (scalarLineCoordinateIsometry x)

theorem scalarGaussianBound_integrable {f : ℝ → ℝ}
    (hc : Continuous f) (C a : ℝ) (hC : 0 < C) (ha : 0 < a)
    (hbound : ∀ s, |f s| ≤ C*Real.exp (-a*s^2)) : Integrable f := by
  have hlift := (scalarGaussianBound_lift C a hC ha hbound).integrable
    (hc.comp scalarLineCoordinateIsometry.continuous)
  exact (scalarLineCoordinateIsometry.measurePreserving.integrable_comp_emb
    scalarLineCoordinateIsometry.toHomeomorph.measurableEmbedding (g := f)).1 hlift

theorem scalarGaussianBound_integrable_mul_log {f : ℝ → ℝ}
    (hc : Continuous f) (hp : ∀ s, 0 < f s)
    (C a : ℝ) (hC : 0 < C) (ha : 0 < a)
    (hbound : ∀ s, |f s| ≤ C*Real.exp (-a*s^2)) :
    Integrable (fun s => f s*Real.log (f s)) := by
  have hlift := (scalarGaussianBound_lift C a hC ha hbound).integrable_mul_log
    (hc.comp scalarLineCoordinateIsometry.continuous) (fun x => hp _)
  exact (scalarLineCoordinateIsometry.measurePreserving.integrable_comp_emb
    scalarLineCoordinateIsometry.toHomeomorph.measurableEmbedding
      (g := fun s => f s*Real.log (f s))).1 hlift

theorem scalarGaussianBound_integrable_sq_mul {f : ℝ → ℝ}
    (hc : Continuous f) (C a : ℝ) (hC : 0 < C) (ha : 0 < a)
    (hbound : ∀ s, |f s| ≤ C*Real.exp (-a*s^2)) :
    Integrable (fun s => s^2*f s) := by
  have hlift := (scalarGaussianBound_lift C a hC ha hbound).norm_sq_mul.integrable
    ((continuous_norm.pow 2).mul (hc.comp scalarLineCoordinateIsometry.continuous))
  have hcomp : Integrable (fun x : E 1 => (scalarLineCoordinateIsometry x)^2*f (scalarLineCoordinateIsometry x)) := by
    simpa only [lineCoordinateIsometry_sq] using hlift
  exact (scalarLineCoordinateIsometry.measurePreserving.integrable_comp_emb
    scalarLineCoordinateIsometry.toHomeomorph.measurableEmbedding
      (g := fun s => s^2*f s)).1 hcomp

theorem scalarGaussianBound_memLp_klDiv_finite {f : ℝ → ℝ}
    (hc : Continuous f) (hp : ∀ s, 0 < f s) (hm : (∫ s, f s)=1)
    (C a : ℝ) (hC : 0 < C) (ha : 0 < a)
    (hbound : ∀ s, |f s| ≤ C*Real.exp (-a*s^2)) :
    MemLp id 2 (positiveDensityLaw f) ∧
      klDiv (positiveDensityLaw f) (gaussianReal 0 1) ≠ (⊤ : ℝ≥0∞) := by
  have hi := scalarGaussianBound_integrable hc C a hC ha hbound
  have hlog := scalarGaussianBound_integrable_mul_log hc hp C a hC ha hbound
  have hsecond := scalarGaussianBound_integrable_sq_mul hc C a hC ha hbound
  exact ⟨positiveDensityLaw_memLp_two hc hp hsecond,
    positiveDensityLaw_klDiv_finite hc hi hp hm hlog hsecond⟩

#print axioms scalarGaussianBound_integrable_mul_log
#print axioms scalarGaussianBound_memLp_klDiv_finite
end CubeSections
