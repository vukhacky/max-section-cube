import CubeSections.Analysis.GaussianQuantile
import CubeSections.Analysis.FrameLiftEnergy
import CubeSections.LinearAlgebra.WeightedGram
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-! Actual Gaussian transport on an open intersection of frame slabs. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Matrix

namespace CubeSections

/-- The normalized row functional, including zero rows. -/
def normalizedFrameFunctional {n k : ℕ} (U : Frame n k) (i : Fin n) : E k →L[ℝ] ℝ :=
  innerSL ℝ ((Real.sqrt (leverage U i))⁻¹ • rowVector U i)

@[simp] theorem normalizedFrameFunctional_apply {n k : ℕ} (U : Frame n k) (i : Fin n) (x : E k) :
    normalizedFrameFunctional U i x = normalizedFrameCoordinate U i x := rfl

def frameSlabInterior {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) : Set (E k) :=
  {x | ∀ i, normalizedFrameCoordinate U i x ∈ Ioo (-r i) (r i)}

def frameQuantileCoordinates {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) (x : E k) : Fin n → ℝ :=
  fun i => intervalGaussianTransport (r i) (normalizedFrameCoordinate U i x)

/-- Barthe's actual frame transport, written in the unnormalized row coordinates. -/
def frameGaussianTransport {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) (x : E k) : E k :=
  ∑ i, (Real.sqrt (leverage U i) * frameQuantileCoordinates U r x i) • rowVector U i

/-- The positive coordinate derivatives entering the actual Jacobian. -/
def frameQuantileSlope {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) (x : E k) (i : Fin n) : ℝ :=
  (2 * r i * gaussianPDFReal 0 1 (frameQuantileCoordinates U r x i))⁻¹

/-- A weighted sum of the actual row rank-one operators. -/
def frameWeightedOperator {n k : ℕ} (U : Frame n k) (w : Fin n → ℝ) : E k →L[ℝ] E k :=
  ∑ i, w i • (innerSL ℝ (rowVector U i)).smulRight (rowVector U i)

theorem frameSlabInterior_isOpen {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) :
    IsOpen (frameSlabInterior U r) := by
  have heq : frameSlabInterior U r = ⋂ i, (normalizedFrameCoordinate U i) ⁻¹' Ioo (-r i) (r i) := by
    ext x; simp [frameSlabInterior]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_Ioo.preimage (normalizedFrameFunctional U i).continuous

theorem frameSlabInterior_convex {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) :
    Convex ℝ (frameSlabInterior U r) := by
  have heq : frameSlabInterior U r = ⋂ i, (normalizedFrameCoordinate U i) ⁻¹' Ioo (-r i) (r i) := by
    ext x; simp [frameSlabInterior]
  rw [heq]
  apply convex_iInter
  intro i
  exact (convex_Ioo (-r i) (r i)).linear_preimage (normalizedFrameFunctional U i).toLinearMap

theorem frameQuantileSlope_pos {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : E k) (i : Fin n) : 0 < frameQuantileSlope U r x i := by
  unfold frameQuantileSlope
  exact inv_pos.mpr (mul_pos (mul_pos (by norm_num) (hr i))
    (ProbabilityTheory.gaussianPDFReal_pos 0 1 _ (by norm_num)))

theorem rowVector_eq_zero_of_leverage_eq_zero {n k : ℕ} (U : Frame n k) (i : Fin n)
    (hi : leverage U i = 0) : rowVector U i = 0 := by
  apply norm_eq_zero.mp
  rw [rowVector_norm, hi, Real.sqrt_zero]

theorem frameGaussianTransport_eq_adjoint {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ) (x : E k) :
    frameGaussianTransport U r x = frameAdjoint U (liftedScores U (frameQuantileCoordinates U r x)) := by
  apply ext_inner_right ℝ
  intro y
  rw [frameGaussianTransport, sum_inner, frameAdjoint,
    ContinuousLinearMap.adjoint_inner_left U.toContinuousLinearMap y]
  simp_rw [real_inner_smul_left, rowVector_inner]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, liftedScores_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

theorem frameWeightedOperator_apply {n k : ℕ} (U : Frame n k) (w : Fin n → ℝ) (h : E k) :
    frameWeightedOperator U w h = ∑ i, (w i * (U h) i) • rowVector U i := by
  simp [frameWeightedOperator, ContinuousLinearMap.sum_apply, rowVector_inner, smul_smul]

theorem hasFDerivAt_frameQuantileCoordinates {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) {x : E k} (hx : x ∈ frameSlabInterior U r) (i : Fin n) :
    HasFDerivAt (fun y => frameQuantileCoordinates U r y i)
      (frameQuantileSlope U r x i • normalizedFrameFunctional U i) x := by
  simpa only [frameQuantileCoordinates, frameQuantileSlope, Function.comp_def,
    normalizedFrameFunctional_apply] using
    (hasDerivAt_intervalGaussianTransport (hr i) (hx i)).comp_hasFDerivAt x
      (normalizedFrameFunctional U i).hasFDerivAt

theorem hasFDerivAt_frameGaussianTransport {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) {x : E k} (hx : x ∈ frameSlabInterior U r) :
    HasFDerivAt (frameGaussianTransport U r)
      (frameWeightedOperator U (frameQuantileSlope U r x)) x := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((hasFDerivAt_frameQuantileCoordinates U r hr hx i).const_mul (Real.sqrt (leverage U i))).smul_const
      (rowVector U i))
  convert h using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro v
    rw [frameWeightedOperator_apply]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hc : leverage U i = 0
    · simp [rowVector_eq_zero_of_leverage_eq_zero U i hc]
    · have hs : Real.sqrt (leverage U i) ≠ 0 := by
        exact ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne (leverage_nonneg U i) (Ne.symm hc)))
      simp only [normalizedFrameFunctional_apply, normalizedFrameCoordinate_eq]
      congr 1
      field_simp

/-- The exact derivative matrix in the canonical orthonormal coordinates. -/
theorem frameWeightedOperator_matrix {n k : ℕ} (U : Frame n k) (w : Fin n → ℝ) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis (frameWeightedOperator U w).toLinearMap =
      weightedGram (frameMatrix U) w := by
  ext a b
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, OrthonormalBasis.coe_toBasis,
    ContinuousLinearMap.coe_coe, frameWeightedOperator_apply,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, rowVector_apply, weightedGram_apply, frameMatrix]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem frameGaussianTransport_jacobian_posDef {n k : ℕ} (U : Frame n k) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) {x : E k} (hx : x ∈ frameSlabInterior U r) :
    (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis (fderiv ℝ (frameGaussianTransport U r) x).toLinearMap).PosDef := by
  rw [(hasFDerivAt_frameGaussianTransport U r hr hx).fderiv, frameWeightedOperator_matrix]
  exact frame_weightedGram_posDef U _ (frameQuantileSlope_pos U r hr x)

end CubeSections
