import CubeSections.Analysis.FrameQuantileInjective
import Mathlib.MeasureTheory.Function.Jacobian

/-! Change of variables for the actual, injective Gaussian frame transport. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubeSections

def frameGaussianJacobian {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) (x : E k) : ℝ :=
  (weightedGram (frameMatrix U) (frameQuantileSlope U r x)).det

theorem frameWeightedOperator_det {n k : ℕ} (U : Frame n k) (w : Fin n → ℝ) :
    (frameWeightedOperator U w).toLinearMap.det = (weightedGram (frameMatrix U) w).det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin k) ℝ).toBasis,
    frameWeightedOperator_matrix]

theorem frameGaussianJacobian_pos {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : E k) : 0 < frameGaussianJacobian U r x :=
  (frame_weightedGram_posDef U _ (frameQuantileSlope_pos U r hr x)).det_pos

theorem frameWeightedOperator_abs_det {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : E k) :
    |(frameWeightedOperator U (frameQuantileSlope U r x)).toLinearMap.det| =
      frameGaussianJacobian U r x := by
  rw [frameWeightedOperator_det]
  exact abs_of_pos (frameGaussianJacobian_pos U r hr x)

theorem frameGaussianTransport_det_fderiv {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) {x : E k} (hx : x ∈ frameSlabInterior U r) :
    (fderiv ℝ (frameGaussianTransport U r) x).toLinearMap.det = frameGaussianJacobian U r x := by
  rw [(hasFDerivAt_frameGaussianTransport U r hr hx).fderiv, frameWeightedOperator_det]
  rfl

theorem frameGaussianTransport_image_measurable {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    MeasurableSet (frameGaussianTransport U r '' frameSlabInterior U r) :=
  measurable_image_of_fderivWithin (frameSlabInterior_isOpen U r).measurableSet
    (fun x hx => (hasFDerivAt_frameGaussianTransport U r hr hx).hasFDerivWithinAt)
    (frameGaussianTransport_injOn U r hr)

/-- Exact pushforward of the Jacobian-weighted Lebesgue measure. -/
theorem frameGaussianTransport_map_jacobian {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    Measure.map (frameGaussianTransport U r)
      ((volume.restrict (frameSlabInterior U r)).withDensity
        (fun x => ENNReal.ofReal (frameGaussianJacobian U r x))) =
      volume.restrict (frameGaussianTransport U r '' frameSlabInterior U r) := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure (E k))
    (frameSlabInterior_isOpen U r).measurableSet.nullMeasurableSet
    (fun x hx => (hasFDerivAt_frameGaussianTransport U r hr hx).hasFDerivWithinAt)
    (frameGaussianTransport_injOn U r hr)
  simpa only [frameWeightedOperator_abs_det U r hr] using h

theorem frameGaussianTransport_lintegral_image {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (g : E k → ℝ≥0∞) :
    (∫⁻ y in frameGaussianTransport U r '' frameSlabInterior U r, g y) =
      ∫⁻ x in frameSlabInterior U r,
        ENNReal.ofReal (frameGaussianJacobian U r x) * g (frameGaussianTransport U r x) := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure (E k))
    (frameSlabInterior_isOpen U r).measurableSet
    (fun x hx => (hasFDerivAt_frameGaussianTransport U r hr hx).hasFDerivWithinAt)
    (frameGaussianTransport_injOn U r hr) g
  simpa only [frameWeightedOperator_abs_det U r hr] using h

theorem frameGaussianTransport_integrable_image_iff {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (g : E k → ℝ) :
    IntegrableOn g (frameGaussianTransport U r '' frameSlabInterior U r) ↔
      IntegrableOn (fun x => frameGaussianJacobian U r x * g (frameGaussianTransport U r x))
        (frameSlabInterior U r) := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (volume : Measure (E k))
    (frameSlabInterior_isOpen U r).measurableSet
    (fun x hx => (hasFDerivAt_frameGaussianTransport U r hr hx).hasFDerivWithinAt)
    (frameGaussianTransport_injOn U r hr) g
  simpa only [frameWeightedOperator_abs_det U r hr, smul_eq_mul] using h

theorem frameGaussianTransport_integral_image {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (g : E k → ℝ) :
    (∫ y in frameGaussianTransport U r '' frameSlabInterior U r, g y) =
      ∫ x in frameSlabInterior U r,
        frameGaussianJacobian U r x * g (frameGaussianTransport U r x) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure (E k))
    (frameSlabInterior_isOpen U r).measurableSet
    (fun x hx => (hasFDerivAt_frameGaussianTransport U r hr hx).hasFDerivWithinAt)
    (frameGaussianTransport_injOn U r hr) g
  simpa only [frameWeightedOperator_abs_det U r hr, smul_eq_mul] using h

end CubeSections
