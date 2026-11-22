import CubeSections.Analysis.TransportDensity
import CubeSections.Analysis.TransportIntegrand
import CubeSections.Analysis.FrameQuantileMoments

/-! Integrability of the actual determinant production and orthogonal residual. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace CubeSections

@[fun_prop] theorem measurable_frameTransportLogProduction {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : Measurable (frameTransportLogProduction U r) := by
  have heq : frameTransportLogProduction U r = fun x => Real.log (frameGaussianJacobian U r x) -
      ∑ i, leverage U i * Real.log (frameQuantileSlope U r x i) :=
    funext (frameTransportLogProduction_eq U r hr)
  rw [heq]
  fun_prop

theorem frameTransportLogProduction_exp_bound {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : E k) :
    frameTransportLogProduction U r x ≤ Real.exp (frameSlabLogFactor U r) *
      (frameGaussianJacobian U r x * euclideanGaussianDensity k (frameGaussianTransport U r x)) := by
  have heq : Real.exp (frameSlabLogFactor U r) *
      (frameGaussianJacobian U r x * euclideanGaussianDensity k (frameGaussianTransport U r x)) =
      Real.exp (frameTransportLogProduction U r x + frameTransportResidualEnergy U r x / 2) := by
    rw [mul_comm (frameGaussianJacobian U r x), frameTransport_density_jacobian U r hr, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  linarith [Real.add_one_le_exp (frameTransportLogProduction U r x + frameTransportResidualEnergy U r x / 2),
    frameTransportResidualEnergy_nonneg U r x]

theorem integrableOn_frameTransportLogProduction {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    IntegrableOn (frameTransportLogProduction U r) (frameSlabInterior U r) := by
  have hI := (frameGaussianTransport_integrable_image_iff U r hr (euclideanGaussianDensity k)).mp
    (euclideanGaussianDensity_integrable k).integrableOn
  apply (hI.const_mul (Real.exp (frameSlabLogFactor U r))).mono'
    (measurable_frameTransportLogProduction U r hr).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (frameTransportLogProduction_nonneg U r x)]
  exact frameTransportLogProduction_exp_bound U r hr x

theorem integrable_frameTransportLogProduction {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    Integrable (frameTransportLogProduction U r) (frameSlabUniform U r) :=
  (integrableOn_frameTransportLogProduction U r hr).smul_measure
    (by simpa only [ENNReal.inv_ne_top] using (ne_of_gt (frameSlabInterior_mass_pos U r hr)))

theorem integrable_frameTransportResidualEnergy {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    Integrable (frameTransportResidualEnergy U r) (frameSlabUniform U r) :=
  integrable_frameQuantile_residual_sq U r hr

end CubeSections
