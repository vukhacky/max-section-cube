import CubeSections.Geometry.AffineSections
import CubeSections.Geometry.Continuity

/-!
# Continuity of the actual affine-section volume at the central fiber

This concerns the specified pointwise fiber-volume representative. It does not
deduce pointwise values from almost-everywhere equality of density functions.
Continuity is asserted at the central offset only; arbitrary boundary offsets
can behave differently, particularly when a row vanishes.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CubeSections

theorem affineSlab_subset_ball {n k : ℕ} (U : Frame n k) (y : E n)
    {R r : ℝ} (hR : cube n ⊆ Metric.closedBall (0 : E n) R) (hr : ‖y‖ ≤ r) :
    affineSlab U y ⊆ Metric.closedBall (0 : E k) (R + r) := by
  intro x hx
  change dist x 0 ≤ R + r
  rw [dist_zero_right]
  have h : ‖y + U x‖ ≤ R := by simpa using hR hx
  calc
    ‖x‖ = ‖U x‖ := (U.norm_map x).symm
    _ = ‖(y + U x) - y‖ := by simp
    _ ≤ ‖y + U x‖ + ‖y‖ := norm_sub_le _ _
    _ ≤ R + r := add_le_add h hr

theorem eventually_affine_coordinate_slab_iff {n k : ℕ} (U : Frame n k)
    (x : E k) (i : Fin n) (h : |(U x) i| ≠ (1 : ℝ) / 2) :
    ∀ᶠ (y : E n) in 𝓝 (0 : E n),
      (|(y + U x) i| ≤ (1 : ℝ) / 2 ↔ |(U x) i| ≤ (1 : ℝ) / 2) := by
  have hc : Continuous (fun y : E n => |(y + U x) i|) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp
      (continuous_id.add continuous_const)).abs
  have ht : Tendsto (fun y : E n => |(y + U x) i|) (𝓝 (0 : E n)) (𝓝 |(U x) i|) := by
    simpa only [ContinuousAt, zero_add] using hc.continuousAt (x := (0 : E n))
  rcases lt_or_gt_of_ne h with hlt | hgt
  · filter_upwards [ht.eventually_lt_const hlt] with y hy
    exact iff_of_true hy.le hlt.le
  · filter_upwards [ht.eventually_const_lt hgt] with y hy
    exact iff_of_false (not_le_of_gt hy) (not_le_of_gt hgt)

theorem ae_eventually_affineSlab_mem_iff_zero {n k : ℕ} (U : Frame n k) :
    ∀ᵐ x ∂volume, ∀ᶠ (y : E n) in 𝓝 (0 : E n),
      (x ∈ affineSlab U y ↔ x ∈ affineSlab U 0) := by
  filter_upwards [ae_frame_coordinates_ne_boundary U] with x hx
  have h : ∀ i, ∀ᶠ (y : E n) in 𝓝 (0 : E n),
      (|(y + U x) i| ≤ (1 : ℝ) / 2 ↔ |(U x) i| ≤ (1 : ℝ) / 2) :=
    fun i => eventually_affine_coordinate_slab_iff U x i (hx i)
  filter_upwards [Filter.eventually_all.mpr h] with y hy
  change (∀ i, |(y + U x) i| ≤ (1 : ℝ) / 2) ↔
    (∀ i, |((0 : E n) + U x) i| ≤ (1 : ℝ) / 2)
  simpa only [zero_add] using forall_congr' hy

theorem continuousAt_affineMass_zero {n k : ℕ} (U : Frame n k) :
    ContinuousAt (affineMass U) 0 := by
  obtain ⟨R, hR⟩ := (cube_compact n).isBounded.subset_closedBall (0 : E n)
  have he : ∀ᶠ (y : E n) in 𝓝 (0 : E n), ‖y‖ ≤ 1 := by
    filter_upwards [(continuous_norm.continuousAt (x := (0 : E n))).eventually_lt_const
      (by simp : ‖(0 : E n)‖ < (1 : ℝ))] with y hy
    exact hy.le
  have hsub : ∀ᶠ (y : E n) in 𝓝 (0 : E n),
      affineSlab U y ⊆ Metric.closedBall (0 : E k) (R + 1) :=
    he.mono fun y hy => affineSlab_subset_ball U y hR hy
  exact tendsto_measure_of_ae_tendsto_indicator (𝓝 (0 : E n))
    (affineSlab_measurableSet U 0) (affineSlab_measurableSet U)
    measurableSet_closedBall (isCompact_closedBall (0 : E k) (R + 1)).measure_ne_top
    hsub (ae_eventually_affineSlab_mem_iff_zero U)

theorem continuousAt_affineVolume_zero {n k : ℕ} (U : Frame n k) :
    ContinuousAt (affineVolume U) 0 :=
  (ENNReal.continuousAt_toReal (affineMass_ne_top U 0)).comp
    (continuousAt_affineMass_zero U)

end CubeSections
