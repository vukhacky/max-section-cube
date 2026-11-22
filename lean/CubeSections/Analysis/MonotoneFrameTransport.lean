import CubeSections.Analysis.FrameQuantile

/-! Actual frame transport for arbitrary differentiable scalar functions. -/
noncomputable section
open scoped BigOperators InnerProductSpace RealInnerProductSpace
namespace CubeSections

def frameFunctionCoordinates {n k : ℕ} (U : Frame n k) (T : Fin n → ℝ → ℝ)
    (x : E k) (i : Fin n) : ℝ := T i (normalizedFrameCoordinate U i x)

def frameFunctionTransport {n k : ℕ} (U : Frame n k) (T : Fin n → ℝ → ℝ)
    (x : E k) : E k :=
  ∑ i, (Real.sqrt (leverage U i) * frameFunctionCoordinates U T x i) • rowVector U i

theorem frameFunctionTransport_eq_adjoint {n k : ℕ} (U : Frame n k)
    (T : Fin n → ℝ → ℝ) (x : E k) :
    frameFunctionTransport U T x = frameAdjoint U (liftedScores U (frameFunctionCoordinates U T x)) := by
  apply ext_inner_right ℝ
  intro y
  rw [frameFunctionTransport, sum_inner, frameAdjoint,
    ContinuousLinearMap.adjoint_inner_left U.toContinuousLinearMap y]
  simp_rw [real_inner_smul_left, rowVector_inner]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, liftedScores_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

theorem hasFDerivAt_frameFunctionCoordinates {n k : ℕ} (U : Frame n k)
    (T w : Fin n → ℝ → ℝ) (hder : ∀ i s, HasDerivAt (T i) (w i s) s)
    (x : E k) (i : Fin n) :
    HasFDerivAt (fun y => frameFunctionCoordinates U T y i)
      (w i (normalizedFrameCoordinate U i x) • normalizedFrameFunctional U i) x := by
  simpa only [frameFunctionCoordinates, Function.comp_def, normalizedFrameFunctional_apply] using
    (hder i (normalizedFrameCoordinate U i x)).comp_hasFDerivAt x
      (normalizedFrameFunctional U i).hasFDerivAt

theorem hasFDerivAt_frameFunctionTransport {n k : ℕ} (U : Frame n k)
    (T w : Fin n → ℝ → ℝ) (hder : ∀ i s, HasDerivAt (T i) (w i s) s)
    (x : E k) :
    HasFDerivAt (frameFunctionTransport U T)
      (frameWeightedOperator U (fun i => w i (normalizedFrameCoordinate U i x))) x := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((hasFDerivAt_frameFunctionCoordinates U T w hder x i).const_mul (Real.sqrt (leverage U i))).smul_const
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

#print axioms hasFDerivAt_frameFunctionTransport
end CubeSections
