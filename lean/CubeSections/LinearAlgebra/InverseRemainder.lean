import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Abel

/-! The positive trace comparison in the clipped determinant argument.
The cutoff derivative and integration through switching times are handled in
the analytic clipped-path modules. -/
noncomputable section
open scoped MatrixOrder
namespace CubeSections

theorem matrix_inverse_remainder_identity {k : ℕ} (X : Matrix (Fin k) (Fin k) ℝ)
    (hX : X.PosDef) :
    X⁻¹ - (2 : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ) + X =
      (1 - X) * X⁻¹ * (1 - X) := by
  have hdet : IsUnit X.det := isUnit_iff_ne_zero.mpr (ne_of_gt hX.det_pos)
  have hl := Matrix.mul_nonsing_inv X hdet
  have hr := Matrix.nonsing_inv_mul X hdet
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hl, hr, two_smul]
  abel

theorem matrix_inverse_remainder_posSemidef {k : ℕ}
    (X : Matrix (Fin k) (Fin k) ℝ) (hX : X.PosDef) :
    (X⁻¹ - (2 : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ) + X).PosSemidef := by
  rw [matrix_inverse_remainder_identity X hX]
  have h := hX.inv.posSemidef.mul_mul_conjTranspose_same (1 - X)
  have hHerm : (1 - X).IsHermitian := Matrix.isHermitian_one.sub hX.isHermitian
  simpa only [hHerm.eq] using h

theorem trace_mul_nonneg_of_posSemidef {k : ℕ}
    (S H : Matrix (Fin k) (Fin k) ℝ) (hS : S.PosSemidef) (hH : H.PosSemidef) :
    0 ≤ Matrix.trace (S * H) := by
  let R := CFC.sqrt S
  have hR : R.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).isHermitian
  have hsq : R * R = S := by
    simpa only [R, pow_two] using CFC.sq_sqrt S hS.nonneg
  have h := (hH.mul_mul_conjTranspose_same R).trace_nonneg
  rw [hR.eq, Matrix.trace_mul_cycle, hsq] at h
  exact h

theorem clipped_trace_comparison {k : ℕ}
    (S X : Matrix (Fin k) (Fin k) ℝ) (hS : S.PosSemidef) (hX : X.PosDef) :
    Matrix.trace (S * (1 - X)) ≤ Matrix.trace (S * (X⁻¹ - 1)) := by
  have h := trace_mul_nonneg_of_posSemidef S
    (X⁻¹ - (2 : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ) + X) hS
    (matrix_inverse_remainder_posSemidef X hX)
  have heq : S * (X⁻¹ - (2 : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ) + X) =
      S * (X⁻¹ - 1) - S * (1 - X) := by
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, two_smul]
    abel
  rw [heq, Matrix.trace_sub] at h
  exact sub_nonneg.mp h

end CubeSections
