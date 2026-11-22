import CubeSections.Geometry.PairKernel
import CubeSections.Analysis.CouplingLift

/-! An actual orthonormal frame of the complementary subspace, with exact
projectors and complementary leverages. -/

noncomputable section
open Set Classical Module
open scoped InnerProductSpace
namespace CubeSections

theorem frameRange_finrank {n k : ℕ} (U : Frame n k) :
    Module.finrank ℝ U.toLinearMap.range = k := by
  rw [LinearMap.finrank_range_of_inj U.injective, finrank_euclideanSpace_fin]

def frameComplement {n k : ℕ} (U : Frame n k) : Submodule ℝ (E n) :=
  U.toLinearMap.rangeᗮ

theorem frameComplement_finrank {n k : ℕ} (U : Frame n k) :
    Module.finrank ℝ (frameComplement U) = n - k := by
  have h := U.toLinearMap.range.finrank_add_finrank_orthogonal
  rw [frameRange_finrank, finrank_euclideanSpace_fin] at h
  change k + Module.finrank ℝ (frameComplement U) = n at h
  omega

def frameComplementBasis {n k : ℕ} (U : Frame n k) :
    OrthonormalBasis (Fin (n - k)) ℝ (frameComplement U) :=
  (stdOrthonormalBasis ℝ (frameComplement U)).reindex (finCongr (frameComplement_finrank U))

def complementaryFrame {n k : ℕ} (U : Frame n k) : Frame n (n - k) :=
  (frameComplement U).subtypeₗᵢ.comp (frameComplementBasis U).repr.symm.toLinearIsometry

theorem complementaryFrame_mem {n k : ℕ} (U : Frame n k) (x : E (n - k)) :
    complementaryFrame U x ∈ frameComplement U := ((frameComplementBasis U).repr.symm x).property

theorem complementaryFrame_range {n k : ℕ} (U : Frame n k) :
    Set.range (complementaryFrame U) = (frameComplement U : Set (E n)) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact complementaryFrame_mem U z
  · intro hx
    refine ⟨(frameComplementBasis U).repr ⟨x, hx⟩, ?_⟩
    change ↑((frameComplementBasis U).repr.symm ((frameComplementBasis U).repr ⟨x, hx⟩)) = x
    simp

theorem range_complementaryFrame {n k : ℕ} (U : Frame n k) :
    (complementaryFrame U).toLinearMap.range = frameComplement U := by
  apply SetLike.coe_injective
  exact complementaryFrame_range U

theorem frame_projection_range {n k : ℕ} (U : Frame n k) (x : E n) :
    U (frameAdjoint U x) = U.toLinearMap.range.starProjection x := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (show U (frameAdjoint U x) ∈ U.toLinearMap.range from ⟨frameAdjoint U x, rfl⟩)
  rintro _ ⟨y, rfl⟩
  exact frameResidual_inner_frame U x y

theorem complementaryFrame_projection {n k : ℕ} (U : Frame n k) (x : E n) :
    complementaryFrame U (frameAdjoint (complementaryFrame U) x) =
      (frameComplement U).starProjection x := by
  simpa only [range_complementaryFrame] using frame_projection_range (complementaryFrame U) x

theorem frameAdjoint_complementaryFrame {n k : ℕ} (U : Frame n k) (x : E n) :
    frameAdjoint (complementaryFrame U) x =
      (frameComplementBasis U).repr ((frameComplement U).orthogonalProjectionOnto x) := by
  have h := complementaryFrame_projection U x
  have hs : (frameComplementBasis U).repr.symm (frameAdjoint (complementaryFrame U) x) =
      (frameComplement U).orthogonalProjectionOnto x := Subtype.ext h
  have he := congrArg (frameComplementBasis U).repr hs
  simpa only [LinearIsometryEquiv.apply_symm_apply] using he

theorem frame_projectors_add {n k : ℕ} (U : Frame n k) (x : E n) :
    U (frameAdjoint U x) + complementaryFrame U (frameAdjoint (complementaryFrame U) x) = x := by
  rw [frame_projection_range U x, complementaryFrame_projection U x]
  exact U.toLinearMap.range.starProjection_add_starProjection_orthogonal x

theorem frameAdjoint_basis {n k : ℕ} (U : Frame n k) (i : Fin n) :
    frameAdjoint U ((EuclideanSpace.basisFun (Fin n) ℝ) i) = rowVector U i := by
  apply ext_inner_right ℝ
  intro x
  rw [frameAdjoint, ContinuousLinearMap.adjoint_inner_left, rowVector_inner,
    real_inner_comm, EuclideanSpace.inner_basisFun_real]
  rfl

theorem gramProjection_complementaryFrame {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    gramProjection (complementaryFrame U) i j = (if i = j then 1 else 0) - gramProjection U i j := by
  have h := congrArg (fun x : E n => x i)
    (frame_projectors_add U ((EuclideanSpace.basisFun (Fin n) ℝ) j))
  change (U (frameAdjoint U ((EuclideanSpace.basisFun (Fin n) ℝ) j))) i +
    (complementaryFrame U (frameAdjoint (complementaryFrame U) ((EuclideanSpace.basisFun (Fin n) ℝ) j))) i =
    ((EuclideanSpace.basisFun (Fin n) ℝ) j) i at h
  rw [frameAdjoint_basis, frameAdjoint_basis, frame_rowVector_coordinate, frame_rowVector_coordinate] at h
  have hb : ((EuclideanSpace.basisFun (Fin n) ℝ) j) i = (if i = j then 1 else 0) := by
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, eq_comm]
  rw [hb] at h
  linarith

theorem leverage_complementaryFrame {n k : ℕ} (U : Frame n k) (i : Fin n) :
    leverage (complementaryFrame U) i = 1 - leverage U i := by
  simpa only [leverage, ite_true] using gramProjection_complementaryFrame U i i

end CubeSections
