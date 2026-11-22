import CubeSections.Analysis.GaussianLaw
import CubeSections.Geometry.RowVectors

/-! Exact Gaussian score moments on the active coordinate support of an actual frame. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace CubeSections

theorem unitRow_inner_sq {n k : ℕ} (U : Frame n k) (i j : ActiveRow U) :
    ⟪unitRow U i, unitRow U j⟫_ℝ ^ 2 =
      gramProjection U i.val j.val ^ 2 / (leverage U i.val * leverage U j.val) := by
  rw [unitRow, unitRow, real_inner_smul_left, real_inner_smul_right,
    inner_rowVector_rowVector]
  simp only [mul_pow, inv_pow, Real.sq_sqrt (le_of_lt i.property),
    Real.sq_sqrt (le_of_lt j.property)]
  field_simp

theorem integral_unitRow_score_sq {n k : ℕ} (U : Frame n k) (i : ActiveRow U) :
    (∫ x : E k, gaussianScore ⟪unitRow U i, x⟫_ℝ ^ 2 ∂(stdGaussian (E k))) =
      Real.sqrt (3 / 5 : ℝ) :=
  integral_gaussianScore_inner_sq (unitRow U i) (unitRow_norm U i)

theorem integral_unitRows_score_mul {n k : ℕ} (U : Frame n k) (i j : ActiveRow U) :
    (∫ x : E k, gaussianScore ⟪unitRow U i, x⟫_ℝ * gaussianScore ⟪unitRow U j, x⟫_ℝ
      ∂(stdGaussian (E k))) =
      3 / Real.sqrt (16 - gramProjection U i.val j.val ^ 2 /
        (leverage U i.val * leverage U j.val)) := by
  rw [integral_gaussianScore_inner_mul (unitRow U i) (unitRow U j)
    (unitRow_norm U i) (unitRow_norm U j), unitRow_inner_sq]

end CubeSections
