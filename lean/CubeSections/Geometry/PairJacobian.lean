import CubeSections.Geometry.PairComplement

/-! The exact normalized two-row coarea Jacobian is 4*sqrt(cd-P^2). -/
noncomputable section
open Set Classical Module
open scoped Matrix InnerProductSpace
namespace CubeSections

theorem pairComplementMap_comp_adjoint_apply {n k : ℕ} (U : Frame n k)
    (i j : Fin n) (p : PairPlane) :
    (pairComplementMap U i j).comp (pairComplementMap U i j).adjoint p =
      WithLp.toLp 2 (4 * (leverage U i * p.fst + gramProjection U i j * p.snd),
        4 * (gramProjection U i j * p.fst + leverage U j * p.snd)) := by
  rw [LinearMap.comp_apply, pairComplementMap_adjoint]
  change pairEuclideanMap U i j (pairAdjointVector U i j p) = _
  rw [pairEuclideanMap_apply]
  congr 1
  ext <;> simp only [pairAdjointVector, map_add, map_smul, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, frame_rowVector_coordinate, ← gramProjection_symm U i j]
  all_goals
    change _ = _
    dsimp [leverage]
    ring

def pairPlaneBasis : Basis (Fin 2) ℝ PairPlane :=
  (Basis.finTwoProd ℝ).map (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).symm

theorem pairComplementMap_comp_adjoint_matrix {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    LinearMap.toMatrix pairPlaneBasis pairPlaneBasis
      ((pairComplementMap U i j).comp (pairComplementMap U i j).adjoint) =
      !![4 * leverage U i, 4 * gramProjection U i j;
         4 * gramProjection U i j, 4 * leverage U j] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [LinearMap.toMatrix_apply, pairPlaneBasis, pairComplementMap_comp_adjoint_apply,
      Basis.map_apply, Basis.map_repr, Basis.coe_finTwoProd_repr,
      WithLp.fst, WithLp.snd]

theorem pairComplementMap_comp_adjoint_det {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    LinearMap.det ((pairComplementMap U i j).comp (pairComplementMap U i j).adjoint) =
      16 * pairGramDet U i j := by
  rw [← LinearMap.det_toMatrix pairPlaneBasis, pairComplementMap_comp_adjoint_matrix,
    Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold pairGramDet
  ring

theorem pairComplementMap_normDet_sq {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : pairGramDet U i j ≠ 0) :
    (pairComplementMap U i j).normDet ^ 2 = 16 * pairGramDet U i j := by
  let e := pairComplementEquiv U i j hdet
  have hconj := LinearMap.det_conj
    ((pairComplementMap U i j).adjoint.comp (pairComplementMap U i j)) e
  have heq : e.toLinearMap.comp
      (((pairComplementMap U i j).adjoint.comp (pairComplementMap U i j)).comp e.symm.toLinearMap) =
      (pairComplementMap U i j).comp (pairComplementMap U i j).adjoint := by
    ext p
    change e ((pairComplementMap U i j).adjoint (e (e.symm p))) =
      e ((pairComplementMap U i j).adjoint p)
    rw [e.apply_symm_apply]
  rw [heq] at hconj
  calc
    _ = LinearMap.det ((pairComplementMap U i j).adjoint.comp (pairComplementMap U i j)) :=
      (pairComplementMap U i j).normDet_sq
    _ = LinearMap.det ((pairComplementMap U i j).comp (pairComplementMap U i j).adjoint) := hconj.symm
    _ = _ := pairComplementMap_comp_adjoint_det U i j

theorem pairComplementEquiv_normDet {n k : ℕ} (U : Frame n k) (i j : Fin n)
    (hdet : 0 < pairGramDet U i j) :
    (pairComplementEquiv U i j (ne_of_gt hdet)).toLinearMap.normDet =
      4 * Real.sqrt (pairGramDet U i j) := by
  change (pairComplementMap U i j).normDet = _
  apply (sq_eq_sq₀ (LinearMap.normDet_nonneg _) (by positivity)).mp
  rw [pairComplementMap_normDet_sq U i j (ne_of_gt hdet), mul_pow,
    Real.sq_sqrt hdet.le]
  ring

end CubeSections
