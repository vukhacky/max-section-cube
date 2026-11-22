import CubeSections.Geometry.RowBasis
import CubeSections.Geometry.Blocks
import Mathlib.Tactic.Linarith

/-! Reconstruction requires nonzero rows and signed equality within parallel classes. -/
noncomputable section
open Set Classical Module
open scoped InnerProductSpace BigOperators
namespace CubeSections

def RowsOrthogonalOrSigned {n k : ℕ} (U : Frame n k) : Prop :=
  ∀ i j : Fin n, inner ℝ (rowVector U i) (rowVector U j) = 0 ∨
    rowVector U i = rowVector U j ∨ rowVector U i = -rowVector U j

private theorem basis_index_eq_of_eq_smul {k : ℕ} (b : Basis (Fin k) ℝ (E k))
    (i j : Fin k) (c : ℝ) (h : b i = c • b j) : i = j := by
  by_contra hij
  have h' := congrArg (fun x => b.repr x i) h
  simp [Basis.repr_self_apply, hij, Ne.symm hij] at h'

theorem RowBasis.orthogonal {n k : ℕ} {U : Frame n k} (b : RowBasis U)
    (hrows : RowsOrthogonalOrSigned U) (i j : Fin k) (hij : i ≠ j) :
    inner ℝ (b.basis i) (b.basis j) = 0 := by
  have h := hrows (b.index i) (b.index j)
  rw [← b.basis_eq i, ← b.basis_eq j] at h
  rcases h with h | h | h
  · exact h
  · exact (hij (b.basis.injective h)).elim
  · have hs : b.basis i = (-1 : ℝ) • b.basis j := by simpa using h
    exact (hij (basis_index_eq_of_eq_smul b.basis i j (-1) hs)).elim

theorem RowBasis.exists_signed_basisVector {n k : ℕ} {U : Frame n k}
    (b : RowBasis U) (hpos : ∀ i, 0 < leverage U i)
    (hrows : RowsOrthogonalOrSigned U) (i : Fin n) :
    ∃ j : Fin k, ∃ negative : Bool,
      rowVector U i = (if negative then (-1 : ℝ) else 1) • b.basis j := by
  have hv : rowVector U i ≠ 0 := by
    intro hz
    have h := hpos i
    rw [← rowVector_norm_sq, hz] at h
    simp at h
  have hex : ∃ j : Fin k, inner ℝ (rowVector U i) (b.basis j) ≠ 0 := by
    by_contra h
    push Not at h
    have hself : inner ℝ (rowVector U i) (rowVector U i) = 0 := by
      calc
        _ = inner ℝ (rowVector U i)
            (∑ j, b.basis.repr (rowVector U i) j • b.basis j) := by
              rw [b.basis.sum_repr]
        _ = 0 := by
          rw [inner_sum]
          simp only [inner_smul_right, h, mul_zero, Finset.sum_const_zero]
    exact hv (inner_self_eq_zero.mp hself)
  obtain ⟨j, hj⟩ := hex
  have h := hrows i (b.index j)
  rw [← b.basis_eq j] at h
  rcases h with h | h | h
  · exact (hj h).elim
  · exact ⟨j, false, by simpa using h⟩
  · exact ⟨j, true, by simpa using h⟩

theorem exists_signedBlockData {n k : ℕ} (U : Frame n k)
    (hpos : ∀ i, 0 < leverage U i) (hrows : RowsOrthogonalOrSigned U) :
    ∃ d : BlockData n k, Set.range U = d.plane ∧
      ∀ i : Fin n, (d.blockSize (d.block i) : ℝ) * leverage U i = 1 := by
  obtain ⟨b⟩ := exists_rowBasis U
  choose block negative hrow using b.exists_signed_basisVector hpos hrows
  have honto : Function.Surjective block := by
    intro j
    refine ⟨b.index j, ?_⟩
    have h := hrow (b.index j)
    rw [← b.basis_eq j] at h
    exact (basis_index_eq_of_eq_smul b.basis j (block (b.index j)) _ h).symm
  let d : BlockData n k := ⟨block, honto, negative⟩
  have hrowd : ∀ i, rowVector U i = d.sign i • b.basis (d.block i) := hrow
  have horth : ∀ i j : Fin k, i ≠ j → inner ℝ (b.basis i) (b.basis j) = 0 :=
    b.orthogonal hrows
  have hrange : Set.range U = d.plane := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, rfl⟩
      refine ⟨fun j => inner ℝ (b.basis j) x, ?_⟩
      intro i
      rw [← rowVector_inner, hrowd, real_inner_smul_left]
    · rintro y ⟨t, ht⟩
      let x : E k := ∑ j : Fin k,
        (t j / inner ℝ (b.basis j) (b.basis j)) • b.basis j
      have hx : ∀ j : Fin k, inner ℝ (b.basis j) x = t j := by
        intro j
        dsimp [x]
        rw [inner_sum]
        simp only [inner_smul_right]
        rw [Finset.sum_eq_single j]
        · exact div_mul_cancel₀ _ (inner_self_ne_zero.mpr (b.basis.ne_zero j))
        · intro l hl hlj
          rw [horth j l (Ne.symm hlj), mul_zero]
        · intro h
          exact (h (Finset.mem_univ j)).elim
      refine ⟨x, ?_⟩
      ext i
      rw [← rowVector_inner, hrowd, real_inner_smul_left, hx]
      exact (ht i).symm
  have hc : ∀ i, leverage U i = ‖b.basis (d.block i)‖ ^ 2 := by
    intro i
    rw [← rowVector_norm_sq, hrowd, norm_smul, Real.norm_eq_abs,
      d.abs_sign, one_mul]
  have hgram : ∀ i j : Fin n, gramProjection U i j ^ 2 =
      if d.block j = d.block i then leverage U i ^ 2 else 0 := by
    intro i j
    rw [← inner_rowVector_rowVector, hrowd i, hrowd j,
      real_inner_smul_left, inner_smul_right]
    by_cases h : d.block j = d.block i
    · rw [if_pos h, h, real_inner_self_eq_norm_sq, ← hc i]
      simp only [mul_pow, blockSign_sq, one_mul]
    · rw [if_neg h, horth _ _ (Ne.symm h)]
      simp
  refine ⟨d, hrange, ?_⟩
  intro i
  have hs : (d.blockSize (d.block i) : ℝ) * leverage U i ^ 2 = leverage U i := by
    calc
      _ = ∑ j : Fin n, if d.block j = d.block i then leverage U i ^ 2 else 0 := by
        rw [← Finset.sum_filter]
        simp [BlockData.blockSize]
      _ = ∑ j : Fin n, gramProjection U i j ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (hgram i j).symm
      _ = leverage U i := gramProjection_row_sq_sum U i
  apply mul_right_cancel₀ (ne_of_gt (hpos i))
  nlinarith [hs]
end CubeSections
