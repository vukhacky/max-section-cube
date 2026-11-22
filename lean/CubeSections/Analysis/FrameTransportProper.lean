import CubeSections.Analysis.FrameSlabMeasure
import CubeSections.Analysis.FrameQuantileInjective
import CubeSections.Analysis.QuantileJacobian
import CubeSections.Analysis.FrameQuantileRegularity
import Mathlib.Topology.Sequences

/-! Compact containment of bounded inverse images for the actual frame transport. -/

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter
open scoped Topology BigOperators InnerProductSpace RealInnerProductSpace

namespace CubeSections

/-- The monotone scalar transport cannot approach an endpoint while its
centered monotonicity product stays bounded. -/
theorem monotone_surjective_interval_product_bounds {r c M : ℝ} {f : ℝ → ℝ}
    (hr : 0 < r) (hc : 0 < c) (hM : 0 ≤ M)
    (hf : MonotoneOn f (Ioo (-r) r)) (hsurj : SurjOn f (Ioo (-r) r) univ) :
    ∃ a b : ℝ, -r < a ∧ b < r ∧
      ∀ s ∈ Ioo (-r) r, c * (f s - f 0) * s ≤ M → s ∈ Icc a b := by
  let L : ℝ := M / (c * (r / 2)) + 1
  have hcr : 0 < c * (r / 2) := mul_pos hc (by linarith)
  have hL : 0 < L := by dsimp [L]; positivity
  have hid : c * L * (r / 2) = M + c * (r / 2) := by
    dsimp [L]
    field_simp
  obtain ⟨a, ha, hfa⟩ := hsurj (mem_univ (f 0 - L))
  obtain ⟨b, hb, hfb⟩ := hsurj (mem_univ (f 0 + L))
  refine ⟨min (-r / 2) a, max (r / 2) b, ?_, ?_, ?_⟩
  · exact lt_min (by linarith) ha.1
  · exact max_lt (by linarith) hb.2
  · intro s hs hbound
    constructor
    · by_contra h
      have hslt : s < min (-r / 2) a := lt_of_not_ge h
      have hsneg : r / 2 < -s := by linarith [lt_of_lt_of_le hslt (min_le_left _ _)]
      have hfs : f s ≤ f 0 - L := hfa ▸ hf hs ha (le_of_lt (lt_of_lt_of_le hslt (min_le_right _ _)))
      have hgap : L ≤ f 0 - f s := by linarith
      have hprod := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hgap (by linarith : 0 ≤ -s)) hc.le
      have hstrict := mul_lt_mul_of_pos_left hsneg (mul_pos hc hL)
      nlinarith [hcr]
    · by_contra h
      have hslt : max (r / 2) b < s := lt_of_not_ge h
      have hspos : r / 2 < s := lt_of_le_of_lt (le_max_left _ _) hslt
      have hfs : f 0 + L ≤ f s := hfb ▸ hf hb hs (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hslt))
      have hgap : L ≤ f s - f 0 := by linarith
      have hprod := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hgap (by linarith : 0 ≤ s)) hc.le
      have hstrict := mul_lt_mul_of_pos_left hspos (mul_pos hc hL)
      nlinarith [hcr]

theorem frameTransport_centered_product_nonneg {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) {x : E k} (hx : x ∈ frameSlabInterior U r) (i : Fin n) :
    0 ≤ leverage U i *
      (frameQuantileCoordinates U r x i - frameQuantileCoordinates U r 0 i) *
        normalizedFrameCoordinate U i x := by
  have h := monotoneOn_difference_product_nonneg
    (strictMonoOn_intervalGaussianTransport (hr i)).monotoneOn (hx i)
    (zero_mem_frameSlabInterior U r hr i)
  have hzero : normalizedFrameCoordinate U i (0 : E k) = 0 := by
    simp [normalizedFrameCoordinate]
  dsimp [frameQuantileCoordinates]
  simpa only [hzero, sub_zero, mul_assoc] using mul_nonneg (leverage_nonneg U i) h

theorem frameTransport_centered_product_le {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) {x : E k} (hx : x ∈ frameSlabInterior U r)
    {M C : ℝ} (hM : ‖frameGaussianTransport U r x‖ ≤ M) (hC : ‖x‖ ≤ C)
    (i : Fin n) :
    leverage U i * (frameQuantileCoordinates U r x i - frameQuantileCoordinates U r 0 i) *
      normalizedFrameCoordinate U i x ≤ (M + ‖frameGaussianTransport U r 0‖) * C := by
  have hsum := frameGaussianTransport_inner_difference U r x 0
  have hzero (j : Fin n) : normalizedFrameCoordinate U j (0 : E k) = 0 := by
    simp [normalizedFrameCoordinate]
  simp only [sub_zero, hzero] at hsum
  have hterm := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => leverage U j *
      (frameQuantileCoordinates U r x j - frameQuantileCoordinates U r 0 j) *
        normalizedFrameCoordinate U j x)
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
      frameTransport_centered_product_nonneg U r hr hx j) (Finset.mem_univ i)
  change leverage U i * (frameQuantileCoordinates U r x i - frameQuantileCoordinates U r 0 i) *
    normalizedFrameCoordinate U i x ≤ _ at hterm
  have hCS : ⟪frameGaussianTransport U r x - frameGaussianTransport U r 0, x⟫_ℝ ≤
      ‖frameGaussianTransport U r x - frameGaussianTransport U r 0‖ * ‖x‖ :=
    real_inner_le_norm _ _
  have hnorm : ‖frameGaussianTransport U r x - frameGaussianTransport U r 0‖ ≤
      M + ‖frameGaussianTransport U r 0‖ :=
    (norm_sub_le _ _).trans (add_le_add hM le_rfl)
  have hpos : 0 ≤ M + ‖frameGaussianTransport U r 0‖ :=
    le_trans (norm_nonneg _) hnorm
  exact hterm.trans (hsum.symm.le.trans
    (hCS.trans (mul_le_mul hnorm hC (norm_nonneg _) hpos)))

#print axioms monotone_surjective_interval_product_bounds
#print axioms frameTransport_centered_product_nonneg
#print axioms frameTransport_centered_product_le

end CubeSections
