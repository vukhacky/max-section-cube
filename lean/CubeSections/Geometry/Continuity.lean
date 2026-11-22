import CubeSections.Geometry.FrameTopology
import CubeSections.Geometry.Boundary
import CubeSections.Geometry.Attainment
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Topology.Order.Compact

/-!
# Continuity of section volume and existence of maximizing frames

Cube indicators converge away from finitely many coordinate level sets, all
of which are null, including the zero-row case. All pullback sections lie in
one fixed compact ball because every frame preserves the Euclidean norm.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CubeSections

theorem frame_section_measurableSet {n k : ℕ} (U : Frame n k) :
    MeasurableSet (U ⁻¹' cube n) :=
  (cube_compact n).isClosed.measurableSet.preimage U.continuous.measurable

theorem uniform_section_ball (n k : ℕ) :
    ∃ r : ℝ, ∀ U : Frame n k, U ⁻¹' cube n ⊆ Metric.closedBall (0 : E k) r := by
  obtain ⟨r, hr⟩ := (cube_compact n).isBounded.subset_closedBall (0 : E n)
  refine ⟨r, fun U x hx => ?_⟩
  have h := hr hx
  simpa only [Metric.mem_closedBall, dist_zero_right, U.norm_map] using h

theorem eventually_coordinate_slab_iff {n k : ℕ} (U : Frame n k) (x : E k) (i : Fin n)
    (h : |(U x) i| ≠ (1 : ℝ) / 2) :
    ∀ᶠ (V : Frame n k) in 𝓝 U,
      (|(V x) i| ≤ (1 : ℝ) / 2 ↔ |(U x) i| ≤ (1 : ℝ) / 2) := by
  have hc := (continuous_frame_coordinate x i).abs.continuousAt (x := U)
  rcases lt_or_gt_of_ne h with hlt | hgt
  · filter_upwards [hc.eventually_lt_const hlt] with V hV
    exact iff_of_true hV.le hlt.le
  · filter_upwards [hc.eventually_const_lt hgt] with V hV
    exact iff_of_false (not_le_of_gt hV) (not_le_of_gt hgt)

theorem ae_eventually_section_mem_iff {n k : ℕ} (U : Frame n k) :
    ∀ᵐ x ∂volume, ∀ᶠ (V : Frame n k) in 𝓝 U,
      (x ∈ V ⁻¹' cube n ↔ x ∈ U ⁻¹' cube n) := by
  filter_upwards [ae_frame_coordinates_ne_boundary U] with x hx
  have h : ∀ i, ∀ᶠ (V : Frame n k) in 𝓝 U,
      (|(V x) i| ≤ (1 : ℝ) / 2 ↔ |(U x) i| ≤ (1 : ℝ) / 2) :=
    fun i => eventually_coordinate_slab_iff U x i (hx i)
  filter_upwards [Filter.eventually_all.mpr h] with V hV
  exact forall_congr' hV

theorem continuous_sectionMass (n k : ℕ) :
    Continuous (sectionMass : Frame n k → ℝ≥0∞) := by
  obtain ⟨r, hr⟩ := uniform_section_ball n k
  apply continuous_iff_continuousAt.mpr
  intro U
  exact tendsto_measure_of_ae_tendsto_indicator (𝓝 U)
    (frame_section_measurableSet U) frame_section_measurableSet
    measurableSet_closedBall (isCompact_closedBall (0 : E k) r).measure_ne_top
    (Eventually.of_forall hr) (ae_eventually_section_mem_iff U)

theorem continuous_sectionVolume (n k : ℕ) :
    Continuous (sectionVolume : Frame n k → ℝ) := by
  apply continuous_iff_continuousAt.mpr
  intro U
  exact (ENNReal.continuousAt_toReal (sectionMass_ne_top U)).comp
    (continuous_sectionMass n k).continuousAt

def IsMaximizingFrame {n k : ℕ} (U : Frame n k) : Prop :=
  ∀ V : Frame n k, sectionVolume V ≤ sectionVolume U

theorem exists_maximizingFrame {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ U : Frame n k, IsMaximizingFrame U := by
  obtain ⟨U, _, hU⟩ := (frame_isCompact n k).exists_isMaxOn
    ⟨balancedFrame hk hkn, Set.mem_univ _⟩ (continuous_sectionVolume n k).continuousOn
  exact ⟨U, fun V => hU (Set.mem_univ V)⟩

theorem sharpValue_le_of_maximizing {n k : ℕ} (U : Frame n k)
    (hU : IsMaximizingFrame U) (hk : 1 ≤ k) (hkn : k ≤ n) :
    sharpValue n k ≤ sectionVolume U := by
  rw [← balancedFrame_volume hk hkn]
  exact hU (balancedFrame hk hkn)

end CubeSections
