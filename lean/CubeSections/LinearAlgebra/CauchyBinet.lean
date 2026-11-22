import CubeSections.LinearAlgebra.Gram
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Push

/-! Cauchy--Binet expansion using ordered row tuples. Repeated rows carry
zero mass, and the factorial normalization accounts for all orderings. -/
noncomputable section
open scoped BigOperators Matrix
namespace CubeSections

theorem det_rectangular_expansion {n k : ℕ}
    (M : Matrix (Fin k) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ) :
    Matrix.det (M * N) = ∑ f : Fin k → Fin n,
      Matrix.det (M.submatrix id f) * ∏ i, N (f i) i := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
    Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  simp only [Matrix.submatrix_apply, id_eq, Finset.prod_mul_distrib,
    Finset.sum_mul, mul_assoc]

def tuplePermute {n k : ℕ} (σ : Equiv.Perm (Fin k)) :
    (Fin k → Fin n) ≃ (Fin k → Fin n) where
  toFun f := f ∘ σ
  invFun f := f ∘ σ.symm
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp

def tupleMinor {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (f : Fin k → Fin n) : ℝ :=
  Matrix.det (A.submatrix f id)

theorem tupleMinor_permute {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (f : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) :
    tupleMinor A (f ∘ σ) = (Equiv.Perm.sign σ : ℝ) * tupleMinor A f := by
  change Matrix.det ((A.submatrix f id).submatrix σ id) =
    (Equiv.Perm.sign σ : ℝ) * Matrix.det (A.submatrix f id)
  exact Matrix.det_permute σ (A.submatrix f id)

theorem tuple_weight_permute {n k : ℕ} (w : Fin n → ℝ)
    (f : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) :
    (∏ i, w (f (σ i))) = ∏ i, w (f i) := by
  exact Equiv.prod_comp σ (fun i => w (f i))

theorem sum_sq_tupleMinor {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (w : Fin n → ℝ) :
    (∑ f : Fin k → Fin n, tupleMinor A f ^ 2 * ∏ i, w (f i)) =
      (Nat.factorial k : ℝ) * ∑ f : Fin k → Fin n,
        tupleMinor A f * (∏ i, A (f i) i) * ∏ i, w (f i) := by
  have hexp (f : Fin k → Fin n) :
      tupleMinor A f ^ 2 * (∏ i, w (f i)) =
        ∑ σ : Equiv.Perm (Fin k),
          ((Equiv.Perm.sign σ : ℝ) * tupleMinor A f) *
            (∏ i, A (f (σ i)) i) * ∏ i, w (f i) := by
    conv_lhs =>
      rw [pow_two]
      arg 1
      arg 2
      unfold tupleMinor
      rw [Matrix.det_apply']
    simp only [Matrix.submatrix_apply, id_eq, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ hσ
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have hperm (σ : Equiv.Perm (Fin k)) :
      (∑ f : Fin k → Fin n, ((Equiv.Perm.sign σ : ℝ) * tupleMinor A f) *
        (∏ i, A (f (σ i)) i) * ∏ i, w (f i)) =
      ∑ f : Fin k → Fin n, tupleMinor A f * (∏ i, A (f i) i) * ∏ i, w (f i) := by
    calc
      _ = ∑ f : Fin k → Fin n, tupleMinor A (f ∘ σ) *
          (∏ i, A (f (σ i)) i) * ∏ i, w (f (σ i)) := by
        simp_rw [tupleMinor_permute, tuple_weight_permute]
      _ = _ := (tuplePermute (n := n) σ).sum_comp
        (fun f => tupleMinor A f * (∏ i, A (f i) i) * ∏ i, w (f i))
  simp_rw [hperm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]

def weightedGram {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (w : Fin n → ℝ) :
    Matrix (Fin k) (Fin k) ℝ := A.transpose * (Matrix.diagonal w * A)

theorem weightedGram_apply {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (w : Fin n → ℝ) (a b : Fin k) :
    weightedGram A w a b = ∑ i, A i a * w i * A i b := by
  unfold weightedGram
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, Matrix.transpose_apply, mul_assoc]

theorem det_weightedGram_expansion {n k : ℕ}
    (A : Matrix (Fin n) (Fin k) ℝ) (w : Fin n → ℝ) :
    Matrix.det (weightedGram A w) =
      ∑ f : Fin k → Fin n, tupleMinor A f * (∏ i, A (f i) i) * ∏ i, w (f i) := by
  rw [weightedGram, det_rectangular_expansion]
  apply Finset.sum_congr rfl
  intro f hf
  have hdet : Matrix.det (A.transpose.submatrix id f) = tupleMinor A f := by
    rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
    rfl
  rw [hdet]
  simp only [Matrix.diagonal_mul, Finset.prod_mul_distrib]
  ring

def tupleMinorMass {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (f : Fin k → Fin n) : ℝ :=
  tupleMinor A f ^ 2 / (Nat.factorial k : ℝ)

theorem tupleMinor_generating {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (w : Fin n → ℝ) :
    (∑ f : Fin k → Fin n, tupleMinorMass A f * ∏ i, w (f i)) =
      Matrix.det (weightedGram A w) := by
  have hfact : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  simp only [tupleMinorMass, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [sum_sq_tupleMinor, mul_div_cancel_left₀ _ hfact, det_weightedGram_expansion]

theorem tupleMinorMass_nonneg {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (f : Fin k → Fin n) : 0 ≤ tupleMinorMass A f :=
  div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

theorem tupleMinor_eq_zero_of_not_injective {n k : ℕ}
    (A : Matrix (Fin n) (Fin k) ℝ) (f : Fin k → Fin n) (hf : ¬ Function.Injective f) :
    tupleMinor A f = 0 := by
  classical
  obtain ⟨i, j, heq, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
    unfold Function.Injective at hf
    push Not at hf
    exact hf
  apply Matrix.det_zero_of_row_eq hne
  funext a
  simp only [Matrix.submatrix_apply, heq]

theorem tupleMinorMass_eq_zero_of_not_injective {n k : ℕ}
    (A : Matrix (Fin n) (Fin k) ℝ) (f : Fin k → Fin n) (hf : ¬ Function.Injective f) :
    tupleMinorMass A f = 0 := by
  simp [tupleMinorMass, tupleMinor_eq_zero_of_not_injective A f hf]

theorem frame_tupleMinorMass_sum {n k : ℕ} (U : Frame n k) :
    (∑ f : Fin k → Fin n, tupleMinorMass (frameMatrix U) f) = 1 := by
  have h := tupleMinor_generating (frameMatrix U) (fun _ => 1)
  simpa only [Finset.prod_const_one, mul_one, weightedGram, Matrix.diagonal_one,
    Matrix.one_mul, frameMatrix_transpose_mul, Matrix.det_one] using h

end CubeSections
