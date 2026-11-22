import CubeSections.Geometry.PairKernel
import CubeSections.Geometry.LinearDensity
import Mathlib.LinearAlgebra.Basis.Fin

/-! The normalized pair-coordinate map restricted to the orthogonal complement
of its kernel. This is the genuine two-dimensional change of variables. -/
noncomputable section
open Set Classical Module
open scoped BigOperators InnerProductSpace
namespace CubeSections

abbrev PairPlane := WithLp 2 (ℝ × ℝ)

theorem pairPlane_finrank : Module.finrank ℝ PairPlane = 2 := by
  rw [(WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).finrank_eq, Module.finrank_prod]
  simp

def pairEuclideanMap {n k : ℕ} (U : Frame n k) (i j : Fin n) : E k →ₗ[ℝ] PairPlane :=
  (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).symm.toLinearMap.comp (pairCoordinateMap U i j)

@[simp] theorem pairEuclideanMap_apply {n k : ℕ} (U : Frame n k) (i j : Fin n) (x : E k) :
    pairEuclideanMap U i j x = WithLp.toLp 2 (2 * (U x) i, 2 * (U x) j) := rfl

theorem pairEuclideanMap_ker {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    (pairEuclideanMap U i j).ker = pairKernel U i j := by
  ext x
  simp [pairEuclideanMap, pairKernel, LinearMap.mem_ker]

def pairComplementMap {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    (pairKernel U i j)ᗮ →ₗ[ℝ] PairPlane :=
  (pairEuclideanMap U i j).comp (pairKernel U i j)ᗮ.subtype

theorem pairComplementMap_injective {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    Function.Injective (pairComplementMap U i j) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hxK : (x : E k) ∈ pairKernel U i j := by
    have hx' : (x : E k) ∈ (pairEuclideanMap U i j).ker := hx
    simpa only [pairEuclideanMap_ker] using hx'
  apply Subtype.ext
  exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hxK x.property)

theorem pairComplement_finrank {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : pairGramDet U i j ≠ 0) : Module.finrank ℝ (pairKernel U i j)ᗮ = 2 := by
  have h := (pairKernel U i j).finrank_add_finrank_orthogonal
  rw [pairKernel_finrank U i j hdet, finrank_euclideanSpace_fin] at h
  have hk := two_le_dimension_of_pairGramDet_ne_zero U i j hdet
  omega

def pairComplementEquiv {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : pairGramDet U i j ≠ 0) : (pairKernel U i j)ᗮ ≃ₗ[ℝ] PairPlane :=
  LinearMap.linearEquivOfInjective (pairComplementMap U i j)
    (pairComplementMap_injective U i j)
    ((pairComplement_finrank U i j hdet).trans pairPlane_finrank.symm)

@[simp] theorem pairComplementEquiv_apply {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : pairGramDet U i j ≠ 0) (x : (pairKernel U i j)ᗮ) :
    pairComplementEquiv U i j hdet x = pairEuclideanMap U i j x := rfl

theorem pairComplementEquiv_projection {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : pairGramDet U i j ≠ 0) (x : E k) :
    pairComplementEquiv U i j hdet ((pairKernel U i j)ᗮ.orthogonalProjectionOnto x) =
      pairEuclideanMap U i j x := by
  have h := congrArg (pairEuclideanMap U i j)
    ((pairKernel U i j).starProjection_add_starProjection_orthogonal x)
  rw [map_add] at h
  have hz : pairEuclideanMap U i j ((pairKernel U i j).starProjection x) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [pairEuclideanMap_ker]
    exact ((pairKernel U i j).orthogonalProjectionOnto x).property
  rw [hz, zero_add] at h
  exact h

def pairAdjointVector {n k : ℕ} (U : Frame n k) (i j : Fin n) (p : PairPlane) : E k :=
  (2 * p.fst) • rowVector U i + (2 * p.snd) • rowVector U j

theorem pairAdjointVector_mem {n k : ℕ} (U : Frame n k) (i j : Fin n) (p : PairPlane) :
    pairAdjointVector U i j p ∈ (pairKernel U i j)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro x hx
  have hx' := (mem_pairKernel U i j x).mp hx
  rw [pairAdjointVector, inner_add_right, inner_smul_right, inner_smul_right,
    real_inner_comm (rowVector U i) x, real_inner_comm (rowVector U j) x,
    rowVector_inner, rowVector_inner, hx'.1, hx'.2]
  simp

theorem pairComplementMap_adjoint {n k : ℕ} (U : Frame n k) (i j : Fin n) (p : PairPlane) :
    (pairComplementMap U i j).adjoint p =
      ⟨pairAdjointVector U i j p, pairAdjointVector_mem U i j p⟩ := by
  apply ext_inner_right ℝ
  intro x
  rw [LinearMap.adjoint_inner_left]
  change inner ℝ p (pairEuclideanMap U i j x) =
    inner ℝ (pairAdjointVector U i j p) (x : E k)
  rw [pairEuclideanMap_apply, WithLp.prod_inner_apply, pairAdjointVector,
    inner_add_left, real_inner_smul_left, real_inner_smul_left,
    rowVector_inner, rowVector_inner]
  simp only [RCLike.inner_apply, conj_trivial, WithLp.fst, WithLp.snd]
  ring

end CubeSections
