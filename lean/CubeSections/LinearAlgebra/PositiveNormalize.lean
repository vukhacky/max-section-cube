import CubeSections.Geometry.RawMatrix
import Mathlib.Analysis.Matrix.Order

/-! Positive symmetric inverse-square-root normalization, with no row deletion. -/
noncomputable section
open scoped Matrix MatrixOrder InnerProductSpace RealInnerProductSpace
namespace CubeSections

def positiveInvSqrt {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (CFC.sqrt M)⁻¹

theorem positiveSqrt_posDef {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : M.PosDef) :
    (CFC.sqrt M).PosDef :=
  Matrix.isStrictlyPositive_iff_posDef.mp (IsStrictlyPositive.sqrt M hM.isStrictlyPositive)

theorem positiveInvSqrt_posDef {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : M.PosDef) :
    (positiveInvSqrt M).PosDef := (positiveSqrt_posDef M hM).inv

theorem positiveInvSqrt_transpose {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : M.PosDef) :
    (positiveInvSqrt M).transpose = positiveInvSqrt M := by
  have h := (positiveInvSqrt_posDef M hM).isHermitian
  change (positiveInvSqrt M).conjTranspose = positiveInvSqrt M at h
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem positiveInvSqrt_sandwich {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : M.PosDef) :
    positiveInvSqrt M * M * positiveInvSqrt M = 1 := by
  have hs : IsUnit (CFC.sqrt M).det := isUnit_iff_ne_zero.mpr (ne_of_gt (positiveSqrt_posDef M hM).det_pos)
  have heq : CFC.sqrt M * CFC.sqrt M = M := by
    simpa only [pow_two] using CFC.sq_sqrt M hM.posSemidef.nonneg
  unfold positiveInvSqrt
  conv_lhs => arg 1; arg 2; rw [← heq]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hs, Matrix.one_mul,
    Matrix.mul_nonsing_inv _ hs]

theorem positiveInvSqrt_det {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : M.PosDef) :
    (positiveInvSqrt M).det = (Real.sqrt M.det)⁻¹ := by
  rw [positiveInvSqrt, Matrix.det_nonsing_inv, hM.posSemidef.det_sqrt]
  simp

def positiveNormalizedMatrix {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin n) (Fin k) ℝ := A * positiveInvSqrt (A.transpose * A)

theorem positiveNormalizedMatrix_orthonormal {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (hA : (A.transpose * A).PosDef) :
    (positiveNormalizedMatrix A).transpose * positiveNormalizedMatrix A = 1 := by
  unfold positiveNormalizedMatrix
  rw [Matrix.transpose_mul, positiveInvSqrt_transpose _ hA]
  calc
    _ = positiveInvSqrt (A.transpose*A) * (A.transpose*A) * positiveInvSqrt (A.transpose*A) := by
      simp only [Matrix.mul_assoc]
    _ = 1 := positiveInvSqrt_sandwich _ hA

/-- A matrix with orthonormal columns gives the actual Euclidean isometry. -/
def frameOfOrthonormalMatrix {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (hA : A.transpose * A = 1) : Frame n k :=
  A.toEuclideanLin.isometryOfInner (fun x y => by
    have hadj : A.toEuclideanLin.adjoint.comp A.toEuclideanLin = LinearMap.id := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.toEuclideanLin,
        ← Matrix.toLpLin_mul_same, hA, Matrix.toLpLin_one]
    rw [← LinearMap.adjoint_inner_right]
    change inner ℝ x ((A.toEuclideanLin.adjoint.comp A.toEuclideanLin) y) = _
    rw [hadj, LinearMap.id_apply])

@[simp] theorem frameOfOrthonormalMatrix_apply {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (hA : A.transpose * A = 1) (x : E k) :
    frameOfOrthonormalMatrix A hA x = A.toEuclideanLin x := rfl

def positiveNormalizedFrame {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (hA : (A.transpose * A).PosDef) : Frame n k :=
  frameOfOrthonormalMatrix (positiveNormalizedMatrix A) (positiveNormalizedMatrix_orthonormal A hA)

theorem positiveNormalizedMatrix_mul_sqrt {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (hA : (A.transpose * A).PosDef) :
    positiveNormalizedMatrix A * CFC.sqrt (A.transpose * A) = A := by
  have hs : IsUnit (CFC.sqrt (A.transpose * A)).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (positiveSqrt_posDef _ hA).det_pos)
  rw [positiveNormalizedMatrix, positiveInvSqrt, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hs, Matrix.mul_one]

theorem positiveNormalizedFrame_apply_sqrt {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (hA : (A.transpose * A).PosDef) (x : E k) :
    positiveNormalizedFrame A hA ((CFC.sqrt (A.transpose * A)).toEuclideanLin x) =
      A.toEuclideanLin x := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin k) ℝ => M.toEuclideanLin x)
    (positiveNormalizedMatrix_mul_sqrt A hA)
  simpa only [positiveNormalizedFrame, frameOfOrthonormalMatrix_apply, Matrix.toEuclideanLin,
    Matrix.toLpLin_mul_same, LinearMap.comp_apply] using h

theorem positiveNormalizedFrame_range {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (hA : (A.transpose * A).PosDef) :
    Set.range (positiveNormalizedFrame A hA) = Set.range A.toEuclideanLin := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(positiveInvSqrt (A.transpose * A)).toEuclideanLin x, ?_⟩
    change A.toEuclideanLin _ = (A * positiveInvSqrt (A.transpose * A)).toEuclideanLin x
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  · rintro ⟨x, rfl⟩
    exact ⟨(CFC.sqrt (A.transpose * A)).toEuclideanLin x, positiveNormalizedFrame_apply_sqrt A hA x⟩

theorem rawMatrix_eq_toMatrix {n k : ℕ} (R : E k →ₗ[ℝ] E n) :
    rawMatrix R = LinearMap.toMatrix (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis R := by
  ext i j
  simp [rawMatrix, LinearMap.toMatrix_apply]

theorem rawMatrix_toEuclideanLin {n k : ℕ} (R : E k →ₗ[ℝ] E n) :
    (rawMatrix R).toEuclideanLin = R := by
  rw [rawMatrix_eq_toMatrix, Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.toLin_toMatrix]

theorem rawGram_posDef {n k : ℕ} (R : E k →ₗ[ℝ] E n) (hR : Function.Injective R) :
    ((rawMatrix R).transpose * rawMatrix R).PosDef := by
  have hps : ((rawMatrix R).transpose * rawMatrix R).PosSemidef := by
    rw [← gram_eq_rawMatrix_transpose_mul]
    exact Matrix.posSemidef_gram ℝ _
  apply hps.posDef_iff_det_ne_zero.mpr
  rw [← normDet_sq_eq_det_rawMatrix]
  exact pow_ne_zero 2 ((R.normDet_ne_zero_tfae.out 5 1).mp hR)

/-- Canonical positive normalization of the actual raw map. -/
def positiveRawFrame {n k : ℕ} (R : E k →ₗ[ℝ] E n) (hR : Function.Injective R) : Frame n k :=
  positiveNormalizedFrame (rawMatrix R) (rawGram_posDef R hR)

theorem positiveRawFrame_formula {n k : ℕ} (R : E k →ₗ[ℝ] E n)
    (hR : Function.Injective R) (x : E k) :
    positiveRawFrame R hR x =
      R ((positiveInvSqrt ((rawMatrix R).transpose * rawMatrix R)).toEuclideanLin x) := by
  change ((rawMatrix R) * positiveInvSqrt ((rawMatrix R).transpose * rawMatrix R)).toEuclideanLin x = _
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  change (rawMatrix R).toEuclideanLin _ = _
  rw [rawMatrix_toEuclideanLin]

theorem positiveRawFrame_range {n k : ℕ} (R : E k →ₗ[ℝ] E n) (hR : Function.Injective R) :
    Set.range (positiveRawFrame R hR) = Set.range R := by
  rw [positiveRawFrame, positiveNormalizedFrame_range, rawMatrix_toEuclideanLin]

theorem positiveRawFrame_sectionVolume {n k : ℕ} (R : E k →ₗ[ℝ] E n)
    (hR : Function.Injective R) :
    sectionVolume (positiveRawFrame R hR) =
      Real.sqrt (((rawMatrix R).transpose * rawMatrix R).det) * rawVolume R := by
  rw [sectionVolume_eq_normDet_mul_rawVolume R (positiveRawFrame R hR)
    (positiveRawFrame_range R hR), normDet_eq_sqrt_det_rawMatrix]

#print axioms positiveInvSqrt_sandwich
#print axioms positiveInvSqrt_det
#print axioms positiveNormalizedMatrix_orthonormal
#print axioms positiveRawFrame_formula
#print axioms positiveRawFrame_range
#print axioms positiveRawFrame_sectionVolume
end CubeSections
