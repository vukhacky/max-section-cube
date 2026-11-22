import CubeSections.Analysis.FrameTransportProper

/-! A bounded set of transport values has preimages in a compact inner slab. -/

noncomputable section
open Set Filter
open scoped Topology

namespace CubeSections

theorem frameGaussianTransport_bounded_preimage_inner_compact {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ S : Set (E k), IsCompact S ∧ S ⊆ frameSlabInterior U r ∧
      ∀ x ∈ frameSlabInterior U r, ‖frameGaussianTransport U r x‖ ≤ M → x ∈ S := by
  classical
  obtain ⟨C, hCpos, hC⟩ := (frameSlabInterior_bounded U r).exists_pos_norm_le
  let B := (M + ‖frameGaussianTransport U r 0‖) * C
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcoord (i : Fin n) : ∃ a b : ℝ, -r i < a ∧ b < r i ∧
      ∀ x ∈ frameSlabInterior U r, ‖frameGaussianTransport U r x‖ ≤ M →
        normalizedFrameCoordinate U i x ∈ Icc a b := by
    by_cases hi : leverage U i = 0
    · refine ⟨-r i / 2, r i / 2, by linarith [hr i], by linarith [hr i], ?_⟩
      intro x hx hFx
      have hzero : normalizedFrameCoordinate U i x = 0 := by
        rw [normalizedFrameCoordinate_eq, hi]
        simp
      rw [hzero]
      constructor <;> linarith [hr i]
    · have hci : 0 < leverage U i := lt_of_le_of_ne (leverage_nonneg U i) (Ne.symm hi)
      obtain ⟨a,b,ha,hb,hab⟩ := monotone_surjective_interval_product_bounds
        (hr i) hci hB (strictMonoOn_intervalGaussianTransport (hr i)).monotoneOn
        (intervalGaussianTransport_surjOn (hr i))
      refine ⟨a,b,ha,hb,?_⟩
      intro x hx hFx
      apply hab _ (hx i)
      have hbnd := frameTransport_centered_product_le U r hr hx hFx (hC x hx) i
      simpa only [frameQuantileCoordinates, normalizedFrameCoordinate, inner_zero_right] using hbnd
  choose a b ha hb hab using hcoord
  let S : Set (E k) := {x | ∀ i, normalizedFrameCoordinate U i x ∈ Icc (a i) (b i)}
  have hsub : S ⊆ frameSlabInterior U r := by
    intro x hx i
    exact ⟨lt_of_lt_of_le (ha i) (hx i).1, lt_of_le_of_lt (hx i).2 (hb i)⟩
  have hclosed : IsClosed S := by
    have heq : S = ⋂ i, (normalizedFrameCoordinate U i) ⁻¹' Icc (a i) (b i) := by
      ext x
      simp [S]
    rw [heq]
    exact isClosed_iInter (fun i => isClosed_Icc.preimage (normalizedFrameFunctional U i).continuous)
  refine ⟨S, Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨hclosed, (frameSlabInterior_bounded U r).subset hsub⟩, hsub, ?_⟩
  intro x hx hFx i
  exact hab i x hx hFx

theorem frameGaussianTransport_image_isClosed {n k : ℕ}
    (U : Frame n k) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    IsClosed (frameGaussianTransport U r '' frameSlabInterior U r) := by
  apply IsSeqClosed.isClosed
  intro u y hu hy
  obtain ⟨M,hMpos,hM⟩ := hy.cauchySeq.isBounded_range.exists_pos_norm_le
  obtain ⟨S,hSc,hSK,hS⟩ := frameGaussianTransport_bounded_preimage_inner_compact U r hr M hMpos.le
  choose x hx hFx using hu
  have hxS (j : ℕ) : x j ∈ S := hS _ (hx j) (by rw [hFx j]; exact hM _ (mem_range_self j))
  have hFcontinuous : ContinuousOn (frameGaussianTransport U r) S :=
    (contDiffOn_frameGaussianTransport U r hr).continuousOn.mono hSK
  have himg : IsCompact (frameGaussianTransport U r '' S) := hSc.image_of_continuousOn hFcontinuous
  have hyS : y ∈ frameGaussianTransport U r '' S :=
    himg.isClosed.mem_of_tendsto hy (Eventually.of_forall fun j => ⟨x j,hxS j,hFx j⟩)
  exact image_mono hSK hyS

#print axioms frameGaussianTransport_bounded_preimage_inner_compact
#print axioms frameGaussianTransport_image_isClosed

end CubeSections
