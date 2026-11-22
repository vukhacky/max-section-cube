import CubeSections.Geometry.NormalizationFrame
import CubeSections.LinearAlgebra.Gram

/-! Coordinate matrices for actual raw linear maps, and their Gram-volume bridge. -/

noncomputable section
open Set MeasureTheory
open scoped Matrix ENNReal

namespace CubeSections

def rawMatrix {n k : ℕ} (R : E k →ₗ[ℝ] E n) : Matrix (Fin n) (Fin k) ℝ :=
  fun i j => (R (EuclideanSpace.basisFun (Fin k) ℝ j)) i

@[simp] theorem rawMatrix_frame {n k : ℕ} (U : Frame n k) :
    rawMatrix U.toLinearMap = frameMatrix U := rfl

theorem gram_eq_rawMatrix_transpose_mul {n k : ℕ} (R : E k →ₗ[ℝ] E n) :
    Matrix.gram ℝ (fun j => R (EuclideanSpace.basisFun (Fin k) ℝ j)) =
      (rawMatrix R).transpose * rawMatrix R := by
  ext i j
  simp [Matrix.gram_apply, EuclideanSpace.inner_eq_star_dotProduct, rawMatrix,
    Matrix.mul_apply, dotProduct, mul_comm]

theorem normDet_sq_eq_det_rawMatrix {n k : ℕ} (R : E k →ₗ[ℝ] E n) :
    R.normDet ^ 2 = Matrix.det ((rawMatrix R).transpose * rawMatrix R) := by
  have h := R.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin k) ℝ)
  rw [gram_eq_rawMatrix_transpose_mul] at h
  simpa using h

theorem normDet_eq_sqrt_det_rawMatrix {n k : ℕ} (R : E k →ₗ[ℝ] E n) :
    R.normDet = Real.sqrt (Matrix.det ((rawMatrix R).transpose * rawMatrix R)) := by
  rw [← normDet_sq_eq_det_rawMatrix, Real.sqrt_sq R.normDet_nonneg]

theorem injective_of_rawMatrix_det_pos {n k : ℕ} (R : E k →ₗ[ℝ] E n)
    (h : 0 < Matrix.det ((rawMatrix R).transpose * rawMatrix R)) : Function.Injective R := by
  have hn : R.normDet ≠ 0 := by
    intro hz
    have hs := normDet_sq_eq_det_rawMatrix R
    rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
    exact (ne_of_gt h) hs.symm
  exact (R.normDet_ne_zero_tfae.out 1 5).mp hn

theorem normalizedFrame_sectionVolume_rawMatrix {n k : ℕ} (R : E k →ₗ[ℝ] E n)
    (hR : Function.Injective R) :
    sectionVolume (normalizedFrame R hR) =
      Real.sqrt (Matrix.det ((rawMatrix R).transpose * rawMatrix R)) * rawVolume R := by
  rw [sectionVolume_eq_normDet_mul_rawVolume R (normalizedFrame R hR)
    (normalizedFrame_range R hR), normDet_eq_sqrt_det_rawMatrix]

end CubeSections
