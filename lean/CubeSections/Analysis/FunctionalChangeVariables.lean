import CubeSections.Analysis.MonotoneFrameInjective
import CubeSections.Analysis.FrameChangeVariables

/-! Actual change of variables for arbitrary monotone differentiable scalar
functions assembled along an actual orthonormal frame. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubeSections

def frameFunctionJacobian {n k : ℕ} (U : Frame n k) (w : Fin n → ℝ → ℝ) (x : E k) : ℝ :=
  (weightedGram (frameMatrix U) (fun i => w i (normalizedFrameCoordinate U i x))).det

theorem frameFunctionJacobian_pos {n k : ℕ} (U : Frame n k) (w : Fin n → ℝ → ℝ)
    (hw : ∀ i s, 0 < w i s) (x : E k) : 0 < frameFunctionJacobian U w x :=
  (frame_weightedGram_posDef U _ (fun i => hw i (normalizedFrameCoordinate U i x))).det_pos

theorem frameFunctionWeightedOperator_abs_det {n k : ℕ} (U : Frame n k) (w : Fin n → ℝ → ℝ)
    (hw : ∀ i s, 0 < w i s) (x : E k) :
    |(frameWeightedOperator U (fun i => w i (normalizedFrameCoordinate U i x))).toLinearMap.det| =
      frameFunctionJacobian U w x := by
  rw [frameWeightedOperator_det]
  exact abs_of_pos (frameFunctionJacobian_pos U w hw x)

theorem frameFunctionTransport_det_fderiv {n k : ℕ} (U : Frame n k)
    (T w : Fin n → ℝ → ℝ) (hder : ∀ i s, HasDerivAt (T i) (w i s) s) (x : E k) :
    (fderiv ℝ (frameFunctionTransport U T) x).toLinearMap.det = frameFunctionJacobian U w x := by
  rw [(hasFDerivAt_frameFunctionTransport U T w hder x).fderiv, frameWeightedOperator_det]
  rfl

theorem continuous_frameFunctionTransport {n k : ℕ} (U : Frame n k)
    (T w : Fin n → ℝ → ℝ) (hder : ∀ i s, HasDerivAt (T i) (w i s) s) :
    Continuous (frameFunctionTransport U T) :=
  continuous_iff_continuousAt.mpr (fun x => (hasFDerivAt_frameFunctionTransport U T w hder x).continuousAt)

theorem measurable_frameFunctionTransport {n k : ℕ} (U : Frame n k)
    (T w : Fin n → ℝ → ℝ) (hder : ∀ i s, HasDerivAt (T i) (w i s) s) :
    Measurable (frameFunctionTransport U T) := (continuous_frameFunctionTransport U T w hder).measurable

theorem frameFunctionTransport_range_measurable {n k : ℕ} (U : Frame n k)
    (T w : Fin n → ℝ → ℝ) (hder : ∀ i s, HasDerivAt (T i) (w i s) s)
    (hmono : ∀ i, StrictMono (T i)) : MeasurableSet (range (frameFunctionTransport U T)) := by
  have h := measurable_image_of_fderivWithin (s := (univ : Set (E k))) MeasurableSet.univ
    (fun x _ => (hasFDerivAt_frameFunctionTransport U T w hder x).hasFDerivWithinAt)
    (frameFunctionTransport_injective U T hmono).injOn
  simpa only [image_univ] using h

/-- Exact Jacobian pushforward on the full Euclidean domain. -/
theorem frameFunctionTransport_map_jacobian {n k : ℕ} (U : Frame n k)
    (T w : Fin n → ℝ → ℝ) (hder : ∀ i s, HasDerivAt (T i) (w i s) s)
    (hmono : ∀ i, StrictMono (T i)) (hw : ∀ i s, 0 < w i s) :
    Measure.map (frameFunctionTransport U T)
      (volume.withDensity (fun x => ENNReal.ofReal (frameFunctionJacobian U w x))) =
      volume.restrict (range (frameFunctionTransport U T)) := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure (E k))
    (s := (univ : Set (E k))) (MeasurableSet.univ : MeasurableSet (univ : Set (E k))).nullMeasurableSet
    (fun x _ => (hasFDerivAt_frameFunctionTransport U T w hder x).hasFDerivWithinAt)
    (frameFunctionTransport_injective U T hmono).injOn
  simpa only [frameFunctionWeightedOperator_abs_det U w hw, Measure.restrict_univ, image_univ] using h

theorem frameFunctionTransport_lintegral_image {n k : ℕ} (U : Frame n k)
    (T w : Fin n → ℝ → ℝ) (hder : ∀ i s, HasDerivAt (T i) (w i s) s)
    (hmono : ∀ i, StrictMono (T i)) (hw : ∀ i s, 0 < w i s) (g : E k → ℝ≥0∞) :
    (∫⁻ y in range (frameFunctionTransport U T), g y) =
      ∫⁻ x, ENNReal.ofReal (frameFunctionJacobian U w x) * g (frameFunctionTransport U T x) := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure (E k))
    (s := (univ : Set (E k))) MeasurableSet.univ
    (fun x _ => (hasFDerivAt_frameFunctionTransport U T w hder x).hasFDerivWithinAt)
    (frameFunctionTransport_injective U T hmono).injOn g
  simpa only [frameFunctionWeightedOperator_abs_det U w hw, Measure.restrict_univ, image_univ] using h

theorem frameFunctionTransport_integrable_image_iff {n k : ℕ} (U : Frame n k)
    (T w : Fin n → ℝ → ℝ) (hder : ∀ i s, HasDerivAt (T i) (w i s) s)
    (hmono : ∀ i, StrictMono (T i)) (hw : ∀ i s, 0 < w i s) (g : E k → ℝ) :
    IntegrableOn g (range (frameFunctionTransport U T)) ↔
      Integrable (fun x => frameFunctionJacobian U w x * g (frameFunctionTransport U T x)) := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (volume : Measure (E k))
    (s := (univ : Set (E k))) MeasurableSet.univ
    (fun x _ => (hasFDerivAt_frameFunctionTransport U T w hder x).hasFDerivWithinAt)
    (frameFunctionTransport_injective U T hmono).injOn g
  simpa only [frameFunctionWeightedOperator_abs_det U w hw, smul_eq_mul, image_univ,
    integrableOn_univ] using h

theorem frameFunctionTransport_integral_image {n k : ℕ} (U : Frame n k)
    (T w : Fin n → ℝ → ℝ) (hder : ∀ i s, HasDerivAt (T i) (w i s) s)
    (hmono : ∀ i, StrictMono (T i)) (hw : ∀ i s, 0 < w i s) (g : E k → ℝ) :
    (∫ y in range (frameFunctionTransport U T), g y) =
      ∫ x, frameFunctionJacobian U w x * g (frameFunctionTransport U T x) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure (E k))
    (s := (univ : Set (E k))) MeasurableSet.univ
    (fun x _ => (hasFDerivAt_frameFunctionTransport U T w hder x).hasFDerivWithinAt)
    (frameFunctionTransport_injective U T hmono).injOn g
  simpa only [frameFunctionWeightedOperator_abs_det U w hw, smul_eq_mul, Measure.restrict_univ,
    image_univ] using h

end CubeSections
