import CubeSections.Analysis.FrameSlabMeasure
import CubeSections.Analysis.QuantileMoments
import CubeSections.Geometry.BoundedMarginal

/-! Actual slab transport second moments, using finite geometric marginal domination. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace CubeSections

theorem integrableOn_frameQuantileCoordinate_sq {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (i : Fin n) :
    IntegrableOn (fun x => frameQuantileCoordinates U r x i ^ 2) (frameSlabInterior U r) := by
  by_cases hi : 0 < leverage U i
  · let i' : ActiveRow U := ⟨i, hi⟩
    obtain ⟨C, hC⟩ := bounded_unit_marginal_restrict_measure_le
      (frameSlabInterior U r) (frameSlabInterior_bounded U r) (unitRow U i') (unitRow_norm U i')
      (r i) (fun x hx => hx i)
    have hg := ((integrableOn_intervalGaussianTransport_sq (r i) (hr i)).smul_measure_nnreal
      (c := C)).mono_measure hC
    simpa only [IntegrableOn, Function.comp_def, frameQuantileCoordinates, normalizedFrameCoordinate, unitRow, i'] using
      hg.comp_measurable (by fun_prop : Measurable (fun x : E k => inner ℝ (unitRow U i') x))
  · have hi₀ : leverage U i = 0 := le_antisymm (le_of_not_gt hi) (leverage_nonneg U i)
    letI : IsFiniteMeasure (volume.restrict (frameSlabInterior U r)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using (frameSlabInterior_bounded U r).measure_lt_top⟩
    have hconst : (fun x => frameQuantileCoordinates U r x i ^ 2) =
        (fun _ : E k => intervalGaussianTransport (r i) 0 ^ 2) := by
      funext x
      simp [frameQuantileCoordinates, normalizedFrameCoordinate, hi₀]
    rw [hconst]
    exact integrable_const _

theorem integrable_frameQuantileCoordinate_sq {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (i : Fin n) :
    Integrable (fun x => frameQuantileCoordinates U r x i ^ 2) (frameSlabUniform U r) :=
  (integrableOn_frameQuantileCoordinate_sq U r hr i).smul_measure
    (by simpa only [ENNReal.inv_ne_top] using (ne_of_gt (frameSlabInterior_mass_pos U r hr)))

theorem frameQuantile_liftedScores_norm_sq {n k : ℕ} (U : Frame n k) (T : Fin n → ℝ) :
    ‖liftedScores U T‖ ^ 2 = ∑ i, leverage U i * T i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  rw [liftedScores_apply, mul_pow, Real.sq_sqrt (leverage_nonneg U i)]

theorem integrable_frameQuantile_lift_sq {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    Integrable (fun x => ‖liftedScores U (frameQuantileCoordinates U r x)‖ ^ 2) (frameSlabUniform U r) := by
  simp_rw [frameQuantile_liftedScores_norm_sq]
  exact integrable_finsetSum _ (fun i _ => (integrable_frameQuantileCoordinate_sq U r hr i).const_mul _)

theorem frameGaussianTransport_norm_sq_le {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) (x : E k) :
    ‖frameGaussianTransport U r x‖ ^ 2 ≤ ‖liftedScores U (frameQuantileCoordinates U r x)‖ ^ 2 := by
  have h := frame_residual_norm_sq U (liftedScores U (frameQuantileCoordinates U r x))
  rw [← frameGaussianTransport_eq_adjoint] at h
  nlinarith [sq_nonneg ‖frameResidual U (liftedScores U (frameQuantileCoordinates U r x))‖]

theorem integrable_frameGaussianTransport_sq {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    Integrable (fun x => ‖frameGaussianTransport U r x‖ ^ 2) (frameSlabUniform U r) := by
  apply (integrable_frameQuantile_lift_sq U r hr).mono' (by fun_prop)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact frameGaussianTransport_norm_sq_le U r x

theorem memLp_frameGaussianTransport_two {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : MemLp (frameGaussianTransport U r) 2 (frameSlabUniform U r) :=
  (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr (integrable_frameGaussianTransport_sq U r hr)

theorem integrable_frameQuantile_residual_sq {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    Integrable (fun x => ‖frameResidual U (liftedScores U (frameQuantileCoordinates U r x))‖ ^ 2)
      (frameSlabUniform U r) := by
  apply ((integrable_frameQuantile_lift_sq U r hr).sub (integrable_frameGaussianTransport_sq U r hr)).congr
  filter_upwards with x
  simp only [Pi.sub_apply]
  rw [frame_residual_norm_sq, ← frameGaussianTransport_eq_adjoint]

end CubeSections
