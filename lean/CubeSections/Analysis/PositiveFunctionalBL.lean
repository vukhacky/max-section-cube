import CubeSections.Analysis.FunctionalChangeVariables
import CubeSections.Analysis.PositiveDensityTransport
import CubeSections.Analysis.FunctionalDensityAlgebra
import CubeSections.Analysis.FunctionalBLClosure

/-! Geometric functional Brascamp--Lieb for positive continuous densities.
The proof constructs the scalar Gaussian CDF transports, proves their actual
Jacobian and injectivity, and integrates the pointwise determinant inequality.
No functional BL theorem is assumed. Zero rows are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CubeSections

theorem positiveFunctionalBL {n k : ℕ} (U : Frame n k) (f : Fin n → ℝ → ℝ)
    (hc : ∀ i, Continuous (f i)) (hi : ∀ i, Integrable (f i))
    (hp : ∀ i s, 0 < f i s) (hnorm : ∀ i, ∫ s, f i s = 1) :
    Integrable (frameFunctionProduct U f) ∧
      (∫ x : E k, frameFunctionProduct U f x) ≤ 1 := by
  let T : Fin n → ℝ → ℝ := fun i => densityGaussianTransport (f i)
  let w : Fin n → ℝ → ℝ := fun i => densityGaussianSlope (f i)
  have hd : ∀ i s, HasDerivAt (T i) (w i s) s := fun i =>
    hasDerivAt_densityGaussianTransport (hc i) (hi i) (hp i) (hnorm i)
  have hm : ∀ i, StrictMono (T i) := fun i =>
    strictMono_densityGaussianTransport (hc i) (hi i) (hp i) (hnorm i)
  have hw : ∀ i s, 0 < w i s := fun i => densityGaussianSlope_pos (hp i)
  have hJac := (frameFunctionTransport_integrable_image_iff U T w hd hm hw
    (euclideanGaussianDensity k)).1 (euclideanGaussianDensity_integrable k).restrict
  have hpoint (x : E k) : frameFunctionProduct U f x ≤
      frameFunctionJacobian U w x * euclideanGaussianDensity k (frameFunctionTransport U T x) := by
    have h := functionalGaussian_density_bound U
      (fun i => f i (normalizedFrameCoordinate U i x)) (frameFunctionCoordinates U T x)
      (fun i => hp i _)
    rw [← frameFunctionTransport_eq_adjoint U T x] at h
    simpa only [frameFunctionProduct, frameFunctionJacobian, frameFunctionCoordinates,
      T, w, densityGaussianSlope, mul_comm] using h
  have hnonneg : ∀ x, 0 ≤ frameFunctionProduct U f x :=
    frameFunctionProduct_nonneg U f (fun i s => (hp i s).le)
  have hint : Integrable (frameFunctionProduct U f) :=
    hJac.mono' (continuous_frameFunctionProduct U f hc).aestronglyMeasurable
      (ae_of_all _ (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]; exact hpoint x))
  refine ⟨hint, ?_⟩
  have hu := setIntegral_le_integral
    (s := Set.range (frameFunctionTransport U T)) (euclideanGaussianDensity_integrable k)
    (ae_of_all _ (fun x => (euclideanGaussianDensity_pos k x).le))
  rw [euclideanGaussianDensity_integral,
    frameFunctionTransport_integral_image U T w hd hm hw] at hu
  exact (integral_mono hint hJac hpoint).trans hu

theorem nonnegativeFunctionalBL {n k : ℕ} (U : Frame n k) (f : Fin n → ℝ → ℝ)
    (hc : ∀ i, Continuous (f i)) (hi : ∀ i, Integrable (f i))
    (hp : ∀ i s, 0 ≤ f i s) (hnorm : ∀ i, ∫ s, f i s = 1) :
    Integrable (frameFunctionProduct U f) ∧
      (∫ x : E k, frameFunctionProduct U f x) ≤ 1 :=
  nonnegativeFunctionalBL_of_positive U (positiveFunctionalBL U) f hc hi hp hnorm

#print axioms positiveFunctionalBL
#print axioms nonnegativeFunctionalBL
end CubeSections
