import CubeSections.Classical.SincBrascampLieb
import CubeSections.Classical.SincIntegrability
import CubeSections.Geometry.Lines

/-! The p=2 scalar normalization from the actual two-dimensional diagonal.
This uses unconditional sinc integrability, cube coarea, Fourier inversion,
and the exact diagonal length; it uses no Ball or functional BL hypothesis.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Matrix

namespace CubeSections

def lineCoordinateIsometry : E 1 ≃ₗᵢ[ℝ] ℝ where
  toFun x := x 0
  invFun t := WithLp.toLp 2 (fun _ : Fin 1 => t)
  left_inv x := by
    ext i
    simp only [Subsingleton.elim i (0 : Fin 1)]
  right_inv t := rfl
  map_add' x y := rfl
  map_smul' a x := rfl
  norm_map' x := by
    change ‖x 0‖ = ‖x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_one, Real.norm_eq_abs, sq_abs]

theorem sinc_mul_eq_of_sq_eq (a b t : ℝ) (hab : a^2=b^2) :
    Real.sinc (a*t) = Real.sinc (b*t) := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hab with h | h
  · rw [h]
  · rw [h, neg_mul, Real.sinc_neg]

theorem lineFrame_coordinate (W : Frame n 1) (x : E 1) (i : Fin n) :
    (W x) i = frameMatrix W i 0 * x 0 := by
  rw [frame_coordinate_eq_dotProduct]
  simp only [dotProduct, Fin.sum_univ_one]

theorem lineFrame_sinc_of_half_leverage (W : Frame n 1)
    (hc : ∀ i, leverage W i=1/2) (x : E 1) (i : Fin n) :
    Real.sinc (Real.pi*(W x) i) = Real.sinc (Real.pi*Real.sqrt (1/2 : ℝ)*x 0) := by
  have hs : frameMatrix W i 0 ^ 2 = Real.sqrt (1/2 : ℝ)^2 := by
    have h := leverage_eq_sum_sq W i
    simp only [Fin.sum_univ_one, hc] at h
    rw [← h, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/2)]
  have h := sinc_mul_eq_of_sq_eq (frameMatrix W i 0) (Real.sqrt (1/2 : ℝ))
    (Real.pi*x 0) hs
  rw [lineFrame_coordinate]
  convert h using 1 <;> congr 1 <;> ring

theorem pairLine_cubeSincKernel (W : Frame 2 1)
    (hc : ∀ i, leverage W i=1/2) (x : E 1) :
    cubeSincKernel W x = ballSincIntegrand 2 (Real.sqrt (1/2 : ℝ)*x 0) := by
  simp only [cubeSincKernel, Fin.prod_univ_two, lineFrame_sinc_of_half_leverage W hc,
    ballSincIntegrand, Real.rpow_two, sq_abs]
  rw [← pow_two]
  congr 1
  rw [mul_assoc]

theorem pairLine_cubeAbsSincKernel (W : Frame 2 1)
    (hc : ∀ i, leverage W i=1/2) (x : E 1) :
    cubeAbsSincKernel W x = ballSincIntegrand 2 (Real.sqrt (1/2 : ℝ)*x 0) := by
  rw [← abs_cubeSincKernel, pairLine_cubeSincKernel W hc,
    abs_of_nonneg (ballSincIntegrand_nonneg _ _)]

theorem pairLine_integrable_absSinc (W : Frame 2 1)
    (hc : ∀ i, leverage W i=1/2) : Integrable (cubeAbsSincKernel W) := by
  have hs : Real.sqrt (1/2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hbase := (integrable_ballSincIntegrand 2 (by norm_num)).comp_mul_left' hs
  have hline := lineCoordinateIsometry.measurePreserving.integrable_comp_emb
    lineCoordinateIsometry.toHomeomorph.measurableEmbedding
    (g := fun t : ℝ => ballSincIntegrand 2 (Real.sqrt (1/2 : ℝ)*t))
  apply (hline.2 hbase).congr
  exact ae_of_all _ (fun x => (pairLine_cubeAbsSincKernel W hc x).symm)

theorem pairLine_sincIntegral (W : Frame 2 1)
    (hc : ∀ i, leverage W i=1/2) :
    (∫ x : E 1, cubeSincKernel W x) = scaledSincIntegral (1/2 : ℝ) := by
  simp_rw [pairLine_cubeSincKernel W hc]
  have hline := lineCoordinateIsometry.measurePreserving.integral_comp
    lineCoordinateIsometry.toHomeomorph.measurableEmbedding
    (fun t : ℝ => ballSincIntegrand 2 (Real.sqrt (1/2 : ℝ)*t))
  change (∫ x : E 1, ballSincIntegrand 2 (Real.sqrt (1/2 : ℝ)*lineCoordinateIsometry x)) = _
  rw [hline]
  simp only [scaledSincIntegral, ballSincIntegrand, mul_assoc]
  norm_num

def diagonalPairData : BlockData 2 1 where
  block := fun _ => 0
  onto := by
    intro j
    exact ⟨0, Subsingleton.elim _ _⟩
  negative := fun _ => false

theorem diagonalPair_leverage (i : Fin 2) : leverage diagonalPairData.frame i = 1/2 := by
  rw [leverage_eq_sum_sq]
  simp only [Fin.sum_univ_one]
  have hmat : frameMatrix diagonalPairData.frame i 0 = 1/Real.sqrt (2 : ℝ) := by
    simp [frameMatrix, BlockData.frame_apply, BlockData.sign, diagonalPairData,
      BlockData.blockSize_one, EuclideanSpace.basisFun_apply]
  rw [hmat, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem diagonalPair_volume : sectionVolume diagonalPairData.frame = Real.sqrt 2 := by
  rw [BlockData.sectionVolume_frame_eq_sqrt_prod]
  simp only [Fin.prod_univ_one, BlockData.blockSize_one, Nat.cast_ofNat]

/-- The exact p=2 endpoint, derived independently of Ball's scalar inequality. -/
theorem ballSincIntegral_two : ballSincIntegral 2 = 1 := by
  let U : Frame 2 1 := diagonalPairData.frame
  let W : Frame 2 1 := complementaryFrame U
  have hc (i : Fin 2) : leverage W i=1/2 := by
    change leverage (complementaryFrame diagonalPairData.frame) i=1/2
    rw [leverage_complementaryFrame, diagonalPair_leverage]
    norm_num
  have hFourier := sectionVolume_eq_complementarySincIntegral U
    (pairLine_integrable_absSinc W hc)
  change sectionVolume diagonalPairData.frame = ∫ x : E 1, cubeSincKernel W x at hFourier
  rw [diagonalPair_volume, pairLine_sincIntegral W hc,
    scaledSincIntegral_eq (1/2 : ℝ) (by norm_num)] at hFourier
  norm_num only [one_div_div, div_one] at hFourier
  have hmul := (eq_div_iff (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 1/2)))).1 hFourier
  have hs : Real.sqrt 2 * Real.sqrt (1/2 : ℝ) = 1 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  linarith

#print axioms ballSincIntegral_two
end CubeSections
