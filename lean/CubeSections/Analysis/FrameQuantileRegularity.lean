import CubeSections.Analysis.FrameQuantile
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Explicit C1 regularity of the actual scalar and frame Gaussian transports. -/

noncomputable section
open Set ProbabilityTheory
open scoped ContDiff

namespace CubeSections

theorem continuousOn_deriv_intervalGaussianTransport (r : ℝ) (hr : 0 < r) :
    ContinuousOn (deriv (intervalGaussianTransport r)) (Ioo (-r) r) := by
  have hT : ContinuousOn (intervalGaussianTransport r) (Ioo (-r) r) :=
    fun s hs => (hasDerivAt_intervalGaussianTransport hr hs).continuousAt.continuousWithinAt
  have hpdf : ContinuousOn (fun s => gaussianPDFReal 0 1 (intervalGaussianTransport r s)) (Ioo (-r) r) :=
    continuous_standardGaussianPDF.comp_continuousOn hT
  have h := (continuousOn_const.mul hpdf).inv₀ (fun s _ =>
    ne_of_gt (mul_pos (by positivity : 0 < 2 * r) (gaussianPDFReal_pos 0 1 _ (by norm_num))))
  apply h.congr
  intro s hs
  exact (hasDerivAt_intervalGaussianTransport hr hs).deriv

theorem contDiffOn_intervalGaussianTransport (r : ℝ) (hr : 0 < r) :
    ContDiffOn ℝ 1 (intervalGaussianTransport r) (Ioo (-r) r) := by
  rw [contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn]
  refine ⟨fun s hs => (hasDerivAt_intervalGaussianTransport hr hs).differentiableAt.differentiableWithinAt, ?_⟩
  apply (continuousOn_deriv_intervalGaussianTransport r hr).congr
  intro s hs
  exact derivWithin_of_isOpen (f := intervalGaussianTransport r) isOpen_Ioo hs

theorem continuousOn_frameQuantileSlope {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (i : Fin n) :
    ContinuousOn (fun x => frameQuantileSlope U r x i) (frameSlabInterior U r) := by
  have hT : ContinuousOn (fun x => frameQuantileCoordinates U r x i) (frameSlabInterior U r) :=
    fun x hx => (hasFDerivAt_frameQuantileCoordinates U r hr hx i).continuousAt.continuousWithinAt
  have hpdf := continuous_standardGaussianPDF.comp_continuousOn hT
  exact (continuousOn_const.mul hpdf).inv₀ (fun x _ =>
    ne_of_gt (mul_pos (mul_pos (by norm_num) (hr i) : 0 < 2 * r i) (gaussianPDFReal_pos 0 1 _ (by norm_num))))

theorem continuousOn_frameGaussianDerivative {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    ContinuousOn (fun x => frameWeightedOperator U (frameQuantileSlope U r x)) (frameSlabInterior U r) := by
  unfold frameWeightedOperator
  exact continuousOn_finsetSum _ (fun i _ => (continuousOn_frameQuantileSlope U r hr i).smul continuousOn_const)

theorem continuousOn_fderiv_frameGaussianTransport {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    ContinuousOn (fderiv ℝ (frameGaussianTransport U r)) (frameSlabInterior U r) := by
  apply (continuousOn_frameGaussianDerivative U r hr).congr
  intro x hx
  exact (hasFDerivAt_frameGaussianTransport U r hr hx).fderiv

theorem contDiffOn_frameGaussianTransport {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    ContDiffOn ℝ 1 (frameGaussianTransport U r) (frameSlabInterior U r) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (frameSlabInterior_isOpen U r).uniqueDiffOn]
  refine ⟨by simp, (fun x => frameWeightedOperator U (frameQuantileSlope U r x)), ?_, ?_⟩
  · simpa only [contDiffOn_zero] using continuousOn_frameGaussianDerivative U r hr
  · exact fun x hx => (hasFDerivAt_frameGaussianTransport U r hr hx).hasFDerivWithinAt

end CubeSections
