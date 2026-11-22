import CubeSections.LinearAlgebra.CauchyBinet
import CubeSections.LinearAlgebra.InverseRemainder

/-! Positive weighted frame operators and the row expansion of their traces. -/
noncomputable section
open scoped BigOperators Matrix MatrixOrder
namespace CubeSections

theorem frameMatrix_mulVec_injective {n k : ℕ} (U : Frame n k) :
    Function.Injective (frameMatrix U).mulVec := by
  intro x y h
  have h' := congrArg (fun v => (frameMatrix U).transpose *ᵥ v) h
  simpa only [Matrix.mulVec_mulVec, frameMatrix_transpose_mul, Matrix.one_mulVec] using h'

theorem weightedGram_posSemidef {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) : (weightedGram A w).PosSemidef := by
  have hD : (Matrix.diagonal w).PosSemidef := Matrix.posSemidef_diagonal_iff.mpr hw
  simpa only [weightedGram, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc]
    using hD.conjTranspose_mul_mul_same A

theorem frame_weightedGram_posDef {n k : ℕ} (U : Frame n k)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) : (weightedGram (frameMatrix U) w).PosDef := by
  have hD : (Matrix.diagonal w).PosDef := Matrix.posDef_diagonal_iff.mpr hw
  simpa only [weightedGram, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc]
    using hD.conjTranspose_mul_mul_same (frameMatrix_mulVec_injective U)

theorem weightedGram_sub {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (w v : Fin n → ℝ) :
    weightedGram A (fun i => w i - v i) = weightedGram A w - weightedGram A v := by
  ext a b
  simp only [weightedGram_apply, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem frame_weightedGram_one {n k : ℕ} (U : Frame n k) :
    weightedGram (frameMatrix U) (fun _ => 1) = 1 := by
  simp only [weightedGram, Matrix.diagonal_one, Matrix.one_mul, frameMatrix_transpose_mul]

theorem frame_weightedGram_le_one {n k : ℕ} (U : Frame n k)
    (w : Fin n → ℝ) (hw : ∀ i, w i ≤ 1) : weightedGram (frameMatrix U) w ≤ 1 := by
  rw [Matrix.le_iff, ← frame_weightedGram_one U, ← weightedGram_sub]
  exact weightedGram_posSemidef _ _ (fun i => sub_nonneg.mpr (hw i))

theorem trace_weightedGram_mul {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (w : Fin n → ℝ) (M : Matrix (Fin k) (Fin k) ℝ) :
    Matrix.trace (weightedGram A w * M) = ∑ i, w i * (A i ⬝ᵥ (M *ᵥ A i)) := by
  have hcycle : Matrix.trace (weightedGram A w * M) =
      Matrix.trace (Matrix.diagonal w * ((A * M) * A.transpose)) := by
    calc
      _ = Matrix.trace (A.transpose * (Matrix.diagonal w * (A * M))) := by
        simp only [weightedGram, Matrix.mul_assoc]
      _ = Matrix.trace ((Matrix.diagonal w * (A * M)) * A.transpose) :=
        Matrix.trace_mul_comm _ _
      _ = _ := by rw [Matrix.mul_assoc]
  rw [hcycle]
  change (∑ i, (Matrix.diagonal w * ((A * M) * A.transpose)) i i) = _
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.diagonal_mul]
  congr 1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem weightedGram_const_mul {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (w : Fin n → ℝ) (r : ℝ) :
    weightedGram A (fun i => r * w i) = r • weightedGram A w := by
  ext a b
  simp only [weightedGram_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem trace_weightedGram_mul_weightedGram {n k : ℕ} (U : Frame n k)
    (a b : Fin n → ℝ) :
    Matrix.trace (weightedGram (frameMatrix U) a * weightedGram (frameMatrix U) b) =
      ∑ i, ∑ j, a i * b j * gramProjection U i j ^ 2 := by
  let A := frameMatrix U
  let P := gramProjection U
  have hcycle : Matrix.trace (weightedGram A a * weightedGram A b) =
      Matrix.trace (Matrix.diagonal a * P * Matrix.diagonal b * P) := by
    calc
      _ = Matrix.trace (A.transpose * (Matrix.diagonal a * P * (Matrix.diagonal b * A))) := by
        simp only [weightedGram, P, A, gramProjection, Matrix.mul_assoc]
      _ = Matrix.trace ((Matrix.diagonal a * P * (Matrix.diagonal b * A)) * A.transpose) :=
        Matrix.trace_mul_comm _ _
      _ = _ := by simp only [P, A, gramProjection, Matrix.mul_assoc]
  change Matrix.trace (weightedGram A a * weightedGram A b) = _
  rw [hcycle]
  change (∑ i, (Matrix.diagonal a * P * Matrix.diagonal b * P) i i) = _
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  dsimp [P]
  rw [← gramProjection_symm U i j]
  ring

end CubeSections
