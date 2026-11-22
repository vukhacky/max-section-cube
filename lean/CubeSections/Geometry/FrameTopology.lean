import CubeSections.Semantics
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The compact space of isometric frames

Frames carry the metric induced by the operator norm on continuous linear maps.
The norm-preservation equations define a closed set inside the unit operator
ball. This includes the empty case when the dimensions do not admit a frame.
-/

noncomputable section
open Set Topology
open scoped Topology

namespace CubeSections

instance frameMetricSpace (n k : ℕ) : MetricSpace (Frame n k) :=
  MetricSpace.induced LinearIsometry.toContinuousLinearMap
    LinearIsometry.toContinuousLinearMap_injective inferInstance

theorem frame_toContinuousLinearMap_isometry (n k : ℕ) :
    Isometry (LinearIsometry.toContinuousLinearMap : Frame n k → E k →L[ℝ] E n) :=
  fun _ _ => rfl

theorem frame_toContinuousLinearMap_range (n k : ℕ) :
    Set.range (LinearIsometry.toContinuousLinearMap : Frame n k → E k →L[ℝ] E n) =
      {f | ∀ x, ‖f x‖ = ‖x‖} := by
  ext f
  constructor
  · rintro ⟨U, rfl⟩
    exact U.norm_map
  · intro hf
    exact ⟨{toLinearMap := f.toLinearMap, norm_map' := hf}, rfl⟩

theorem frame_toContinuousLinearMap_closedRange (n k : ℕ) :
    IsClosed (Set.range (LinearIsometry.toContinuousLinearMap : Frame n k → E k →L[ℝ] E n)) := by
  rw [frame_toContinuousLinearMap_range, Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_eq (continuous_eval_const x).norm continuous_const

theorem frame_toContinuousLinearMap_isClosedEmbedding (n k : ℕ) :
    IsClosedEmbedding (LinearIsometry.toContinuousLinearMap : Frame n k → E k →L[ℝ] E n) :=
  ⟨(frame_toContinuousLinearMap_isometry n k).isEmbedding,
    frame_toContinuousLinearMap_closedRange n k⟩

theorem frame_isCompact (n k : ℕ) : IsCompact (Set.univ : Set (Frame n k)) := by
  have hsub : Set.range
      (LinearIsometry.toContinuousLinearMap : Frame n k → E k →L[ℝ] E n) ⊆
      Metric.closedBall (0 : E k →L[ℝ] E n) 1 := by
    rintro _ ⟨U, rfl⟩
    simpa using U.norm_toContinuousLinearMap_le
  have hc := (isCompact_closedBall (0 : E k →L[ℝ] E n) 1).of_isClosed_subset
    (frame_toContinuousLinearMap_closedRange n k) hsub
  simpa using (frame_toContinuousLinearMap_isClosedEmbedding n k).isCompact_preimage hc

instance frameCompactSpace (n k : ℕ) : CompactSpace (Frame n k) := ⟨frame_isCompact n k⟩

theorem continuous_frame_apply {n k : ℕ} (x : E k) :
    Continuous (fun U : Frame n k => U x) := by
  have h : Continuous (fun f : E k →L[ℝ] E n => f x) := continuous_eval_const x
  exact h.comp (frame_toContinuousLinearMap_isometry n k).continuous

theorem continuous_frame_coordinate {n k : ℕ} (x : E k) (i : Fin n) :
    Continuous (fun U : Frame n k => (U x) i) :=
  (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp (continuous_frame_apply x)

end CubeSections
