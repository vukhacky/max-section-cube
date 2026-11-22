import CubeSections.Geometry.RowVectors
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Basis.Basic

/-! A basis selected from the actual row vectors of an isometric frame. -/
noncomputable section
open Set Module
open scoped InnerProductSpace
namespace CubeSections

theorem span_rowVector {n k : ℕ} (U : Frame n k) :
    Submodule.span ℝ (Set.range (rowVector U)) = ⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hUx : U x = 0 := by
    ext i
    have h := (Submodule.mem_orthogonal _ x).mp hx (rowVector U i)
      (Submodule.subset_span (Set.mem_range_self i))
    simpa only [rowVector_inner, PiLp.zero_apply] using h
  apply U.injective
  simpa only [map_zero] using hUx

structure RowBasis {n k : ℕ} (U : Frame n k) where
  index : Fin k → Fin n
  basis : Basis (Fin k) ℝ (E k)
  basis_eq : ∀ j, basis j = rowVector U (index j)

theorem exists_rowBasis {n k : ℕ} (U : Frame n k) : Nonempty (RowBasis U) := by
  classical
  obtain ⟨ι, a, ha, hspan, hlin⟩ := exists_linearIndependent' ℝ (rowVector U)
  letI : Finite ι := Finite.of_injective a ha
  letI : Fintype ι := Fintype.ofFinite ι
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range (rowVector U ∘ a)) := by
    rw [hspan, span_rowVector U]
  let b : Basis ι ℝ (E k) := Basis.mk hlin hsp
  have hc : Fintype.card ι = k := by
    rw [← Module.finrank_eq_card_basis b]
    exact finrank_euclideanSpace_fin
  let e : ι ≃ Fin k := Fintype.equivFinOfCardEq hc
  refine ⟨⟨fun j => a (e.symm j), b.reindex e, ?_⟩⟩
  intro j
  rw [Basis.reindex_apply]
  exact Basis.mk_apply hlin hsp (e.symm j)
end CubeSections
