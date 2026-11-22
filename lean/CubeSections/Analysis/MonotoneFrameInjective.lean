import CubeSections.Analysis.MonotoneFrameTransport
import CubeSections.Analysis.FrameQuantileInjective

/-! Global injectivity of an actual frame transport built from arbitrary
strictly increasing scalar maps. There are no CDF, differentiability, positivity
of row leverage, or bounded-domain assumptions. -/
noncomputable section
open Set
open scoped BigOperators InnerProductSpace RealInnerProductSpace
namespace CubeSections

theorem frameFunctionTransport_inner_difference {n k : ℕ} (U : Frame n k)
    (T : Fin n → ℝ → ℝ) (x y : E k) :
    ⟪frameFunctionTransport U T x - frameFunctionTransport U T y, x-y⟫_ℝ =
      ∑ i, leverage U i * (frameFunctionCoordinates U T x i - frameFunctionCoordinates U T y i) *
        (normalizedFrameCoordinate U i x - normalizedFrameCoordinate U i y) := by
  rw [inner_sub_left, frameFunctionTransport, frameFunctionTransport, sum_inner, sum_inner]
  simp_rw [real_inner_smul_left, rowVector_inner]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [U.map_sub]
  change Real.sqrt (leverage U i) * frameFunctionCoordinates U T x i * ((U x) i - (U y) i) -
    Real.sqrt (leverage U i) * frameFunctionCoordinates U T y i * ((U x) i - (U y) i) = _
  rw [← normalizedFrameCoordinate_scaled U i x, ← normalizedFrameCoordinate_scaled U i y]
  calc
    _ = Real.sqrt (leverage U i)^2 *
      (frameFunctionCoordinates U T x i - frameFunctionCoordinates U T y i) *
      (normalizedFrameCoordinate U i x - normalizedFrameCoordinate U i y) := by ring
    _ = _ := by rw [Real.sq_sqrt (leverage_nonneg U i)]

/-- Strict monotonicity of every scalar map gives injectivity of the entire
frame transport, including frames with zero rows. -/
theorem frameFunctionTransport_injective {n k : ℕ} (U : Frame n k)
    (T : Fin n → ℝ → ℝ) (hT : ∀ i, StrictMono (T i)) :
    Function.Injective (frameFunctionTransport U T) := by
  intro x y hxy
  have hp (i : Fin n) : 0 ≤
      (frameFunctionCoordinates U T x i - frameFunctionCoordinates U T y i) *
        (normalizedFrameCoordinate U i x - normalizedFrameCoordinate U i y) :=
    monotoneOn_difference_product_nonneg ((hT i).monotone.monotoneOn Set.univ)
      (mem_univ _) (mem_univ _)
  have hsum : (∑ i, leverage U i *
      ((frameFunctionCoordinates U T x i - frameFunctionCoordinates U T y i) *
        (normalizedFrameCoordinate U i x - normalizedFrameCoordinate U i y))) = 0 := by
    have h := frameFunctionTransport_inner_difference U T x y
    rw [hxy, sub_self, inner_zero_left] at h
    simpa only [mul_assoc] using h.symm
  have hzero (i : Fin n) : leverage U i *
      ((frameFunctionCoordinates U T x i - frameFunctionCoordinates U T y i) *
        (normalizedFrameCoordinate U i x - normalizedFrameCoordinate U i y)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (leverage_nonneg U j) (hp j))).mp hsum
      i (Finset.mem_univ i)
  apply U.injective
  ext i
  rw [← normalizedFrameCoordinate_scaled U i x, ← normalizedFrameCoordinate_scaled U i y]
  by_cases hi : leverage U i=0
  · simp [hi]
  · congr 1
    by_contra hne
    have hpos := strictMonoOn_difference_product_pos ((hT i).strictMonoOn Set.univ)
      (mem_univ _) (mem_univ _) hne
    have hci : 0 < leverage U i := lt_of_le_of_ne (leverage_nonneg U i) (Ne.symm hi)
    have ht := mul_pos hci hpos
    change 0 < leverage U i *
      ((frameFunctionCoordinates U T x i - frameFunctionCoordinates U T y i) *
        (normalizedFrameCoordinate U i x - normalizedFrameCoordinate U i y)) at ht
    rw [hzero i] at ht
    exact lt_irrefl _ ht

#print axioms frameFunctionTransport_inner_difference
#print axioms frameFunctionTransport_injective
end CubeSections
