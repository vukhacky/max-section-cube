import CubeSections.Analysis.FrameQuantile

/-! Global injectivity of the actual Gaussian frame transport on its slab domain. -/

noncomputable section
open Set
open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace CubeSections

theorem monotoneOn_difference_product_nonneg {f : ℝ → ℝ} {s : Set ℝ}
    (hf : MonotoneOn f s) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    0 ≤ (f x - f y) * (x - y) := by
  rcases le_total x y with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf hx hy h)) (sub_nonpos.mpr h)
  · exact mul_nonneg (sub_nonneg.mpr (hf hy hx h)) (sub_nonneg.mpr h)

theorem strictMonoOn_difference_product_pos {f : ℝ → ℝ} {s : Set ℝ}
    (hf : StrictMonoOn f s) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    0 < (f x - f y) * (x - y) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact mul_pos_of_neg_of_neg (sub_neg.mpr (hf hx hy h)) (sub_neg.mpr h)
  · exact mul_pos (sub_pos.mpr (hf hy hx h)) (sub_pos.mpr h)

theorem frameGaussianTransport_inner_difference {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (x y : E k) :
    ⟪frameGaussianTransport U r x - frameGaussianTransport U r y, x - y⟫_ℝ =
      ∑ i, leverage U i * (frameQuantileCoordinates U r x i - frameQuantileCoordinates U r y i) *
        (normalizedFrameCoordinate U i x - normalizedFrameCoordinate U i y) := by
  rw [inner_sub_left, frameGaussianTransport, frameGaussianTransport, sum_inner, sum_inner]
  simp_rw [real_inner_smul_left, rowVector_inner]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [U.map_sub]
  change Real.sqrt (leverage U i) * frameQuantileCoordinates U r x i * ((U x) i - (U y) i) -
    Real.sqrt (leverage U i) * frameQuantileCoordinates U r y i * ((U x) i - (U y) i) = _
  rw [← normalizedFrameCoordinate_scaled U i x, ← normalizedFrameCoordinate_scaled U i y]
  calc
    _ = Real.sqrt (leverage U i) ^ 2 *
      (frameQuantileCoordinates U r x i - frameQuantileCoordinates U r y i) *
      (normalizedFrameCoordinate U i x - normalizedFrameCoordinate U i y) := by ring
    _ = _ := by rw [Real.sq_sqrt (leverage_nonneg U i)]

/-- Injectivity is proved directly from the monotonicity of the actual scalar
quantiles; no convex-gradient theorem is assumed. -/
theorem frameGaussianTransport_injOn {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) : InjOn (frameGaussianTransport U r) (frameSlabInterior U r) := by
  intro x hx y hy hxy
  have hp (i : Fin n) : 0 ≤
      (frameQuantileCoordinates U r x i - frameQuantileCoordinates U r y i) *
        (normalizedFrameCoordinate U i x - normalizedFrameCoordinate U i y) :=
    monotoneOn_difference_product_nonneg (strictMonoOn_intervalGaussianTransport (hr i)).monotoneOn
      (hx i) (hy i)
  have hsum : (∑ i, leverage U i *
      ((frameQuantileCoordinates U r x i - frameQuantileCoordinates U r y i) *
        (normalizedFrameCoordinate U i x - normalizedFrameCoordinate U i y))) = 0 := by
    have h := frameGaussianTransport_inner_difference U r x y
    rw [hxy, sub_self, inner_zero_left] at h
    simpa only [mul_assoc] using h.symm
  have hzero (i : Fin n) : leverage U i *
      ((frameQuantileCoordinates U r x i - frameQuantileCoordinates U r y i) *
        (normalizedFrameCoordinate U i x - normalizedFrameCoordinate U i y)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (leverage_nonneg U j) (hp j))).mp hsum
      i (Finset.mem_univ i)
  apply U.injective
  ext i
  rw [← normalizedFrameCoordinate_scaled U i x, ← normalizedFrameCoordinate_scaled U i y]
  by_cases hi : leverage U i = 0
  · simp [hi]
  · congr 1
    by_contra hne
    have hpos := strictMonoOn_difference_product_pos
      (strictMonoOn_intervalGaussianTransport (hr i)) (hx i) (hy i) hne
    have hci : 0 < leverage U i := lt_of_le_of_ne (leverage_nonneg U i) (Ne.symm hi)
    have ht := mul_pos hci hpos
    change 0 < leverage U i *
      ((frameQuantileCoordinates U r x i - frameQuantileCoordinates U r y i) *
        (normalizedFrameCoordinate U i x - normalizedFrameCoordinate U i y)) at ht
    rw [hzero i] at ht
    exact lt_irrefl _ ht

end CubeSections
