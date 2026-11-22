import CubeSections.Analysis.GaussianDensity
import CubeSections.Analysis.FrameChangeVariables
import CubeSections.Analysis.QuantileJacobian
import CubeSections.LinearAlgebra.MinorEntropy

/-! Exact density/Jacobian identity for the constructed Gaussian transport. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CubeSections

def frameSlabLogFactor {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) : ℝ :=
  ∑ i, leverage U i * Real.log (2 * r i)

def frameTransportLogProduction {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) (x : E k) : ℝ :=
  determinantRemainder U (fun i => Real.log (frameQuantileSlope U r x i))

def frameTransportResidualEnergy {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) (x : E k) : ℝ :=
  ‖frameResidual U (liftedScores U (frameQuantileCoordinates U r x))‖ ^ 2

theorem liftedScores_norm_sq {n k : ℕ} (U : Frame n k) (T : Fin n → ℝ) :
    ‖liftedScores U T‖ ^ 2 = ∑ i, leverage U i * T i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [liftedScores_apply, mul_pow, Real.sq_sqrt (leverage_nonneg U i)]

theorem frameQuantileSlope_log {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : E k) (i : Fin n) :
    Real.log (frameQuantileSlope U r x i) =
      Real.log (Real.sqrt (2 * Real.pi)) - Real.log (2 * r i) +
        frameQuantileCoordinates U r x i ^ 2 / 2 := by
  have hri := hr i
  unfold frameQuantileSlope frameQuantileCoordinates
  rw [intervalGaussianTransport_log_slope _ _ (hr i), Real.log_div (by positivity) (by positivity)]

theorem frameQuantileSlope_weighted_log {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : E k) :
    (∑ i, leverage U i * Real.log (frameQuantileSlope U r x i)) =
      (k : ℝ) * Real.log (Real.sqrt (2 * Real.pi)) - frameSlabLogFactor U r +
        ‖liftedScores U (frameQuantileCoordinates U r x)‖ ^ 2 / 2 := by
  simp_rw [frameQuantileSlope_log U r hr x, mul_add, mul_sub, ← mul_div_assoc]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_leverage, ← Finset.sum_div, ← liftedScores_norm_sq]
  rfl

theorem frameTransportLogProduction_eq {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : E k) :
    frameTransportLogProduction U r x = Real.log (frameGaussianJacobian U r x) -
      ∑ i, leverage U i * Real.log (frameQuantileSlope U r x i) := by
  unfold frameTransportLogProduction determinantRemainder frameGaussianJacobian
  simp only [Real.exp_log (frameQuantileSlope_pos U r hr x _)]

theorem frameTransportLogProduction_nonneg {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) (x : E k) :
    0 ≤ frameTransportLogProduction U r x := determinantRemainder_nonneg U _

theorem frameTransportResidualEnergy_nonneg {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) (x : E k) :
    0 ≤ frameTransportResidualEnergy U r x := sq_nonneg _

theorem frameTransport_log_density_jacobian {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : E k) :
    Real.log (euclideanGaussianDensity k (frameGaussianTransport U r x)) +
      Real.log (frameGaussianJacobian U r x) =
      -frameSlabLogFactor U r + frameTransportLogProduction U r x +
        frameTransportResidualEnergy U r x / 2 := by
  rw [log_euclideanGaussianDensity, frameTransportLogProduction_eq U r hr,
    frameQuantileSlope_weighted_log U r hr, frameTransportResidualEnergy,
    frame_residual_norm_sq, frameGaussianTransport_eq_adjoint]
  ring

theorem frameTransport_density_jacobian {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : E k) :
    euclideanGaussianDensity k (frameGaussianTransport U r x) * frameGaussianJacobian U r x =
      Real.exp (-frameSlabLogFactor U r + frameTransportLogProduction U r x +
        frameTransportResidualEnergy U r x / 2) := by
  rw [← frameTransport_log_density_jacobian U r hr x, Real.exp_add,
    Real.exp_log (euclideanGaussianDensity_pos _ _), Real.exp_log (frameGaussianJacobian_pos U r hr x)]

theorem frameTransport_density_jacobian_lower {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : E k) :
    Real.exp (-frameSlabLogFactor U r) ≤
      frameGaussianJacobian U r x * euclideanGaussianDensity k (frameGaussianTransport U r x) := by
  rw [mul_comm, frameTransport_density_jacobian U r hr]
  apply Real.exp_le_exp.mpr
  linarith [frameTransportLogProduction_nonneg U r x, frameTransportResidualEnergy_nonneg U r x]

end CubeSections
