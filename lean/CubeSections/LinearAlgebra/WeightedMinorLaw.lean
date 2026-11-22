import CubeSections.LinearAlgebra.WeightedGram
import CubeSections.LinearAlgebra.MinorLaw

/-! Tilted Cauchy--Binet marginals, expressed by the inverse weighted frame operator. -/
noncomputable section
open scoped BigOperators Matrix
namespace CubeSections

theorem det_add_scaled_outer {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    (hM : IsUnit M.det) (v : Fin k → ℝ) (c : ℝ) :
    Matrix.det (M + c • Matrix.vecMulVec v v) =
      Matrix.det M * (1 + c * (v ⬝ᵥ (M⁻¹ *ᵥ v))) := by
  have hfactor : M + c • Matrix.vecMulVec v v =
      M * (1 + c • Matrix.vecMulVec (M⁻¹ *ᵥ v) v) := by
    simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_vecMulVec,
      Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM, Matrix.one_mulVec]
  rw [hfactor, Matrix.det_mul, ← Matrix.smul_vecMulVec, det_one_add_outer]
  congr 2
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem weightedGram_coordinate_perturbation {n k : ℕ}
    (A : Matrix (Fin n) (Fin k) ℝ) (w : Fin n → ℝ) (i : Fin n) (x : ℝ) :
    weightedGram A (fun b => w b * coordinateWeight i x b) =
      weightedGram A w + (x * w i) • Matrix.vecMulVec (A i) (A i) := by
  ext a b
  change weightedGram A (fun t => w t * coordinateWeight i x t) a b =
    weightedGram A w a b + (x * w i) * (A i a * A i b)
  rw [weightedGram_apply, weightedGram_apply]
  simp [coordinateWeight, mul_add, add_mul, Finset.sum_add_distrib,
    mul_ite, ite_mul, mul_assoc, mul_left_comm]

def tiltedMinorMass {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (w : Fin n → ℝ) (f : Fin k → Fin n) : ℝ :=
  tupleMinorMass A f * ∏ a, w (f a)

theorem tiltedMinorMass_sum {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (w : Fin n → ℝ) :
    (∑ f : Fin k → Fin n, tiltedMinorMass A w f) = Matrix.det (weightedGram A w) :=
  tupleMinor_generating A w

theorem tilted_coordinate_product {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (w : Fin n → ℝ) (f : Fin k → Fin n) (i : Fin n) (x : ℝ) :
    tupleMinorMass A f * (∏ a, w (f a) * coordinateWeight i x (f a)) =
      tiltedMinorMass A w f * (1 + x * tupleHit f i) := by
  classical
  by_cases hf : Function.Injective f
  · rw [Finset.prod_mul_distrib, prod_coordinateWeight_of_injective f hf]
    simp only [tiltedMinorMass, mul_assoc]
  · simp [tupleMinorMass_eq_zero_of_not_injective A f hf, tiltedMinorMass]

theorem tiltedMinorMarginal {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (w : Fin n → ℝ) (hM : IsUnit (weightedGram A w).det) (i : Fin n) :
    (∑ f : Fin k → Fin n, tiltedMinorMass A w f * tupleHit f i) =
      Matrix.det (weightedGram A w) * w i * (A i ⬝ᵥ ((weightedGram A w)⁻¹ *ᵥ A i)) := by
  have h := tupleMinor_generating A (fun b => w b * coordinateWeight i 1 b)
  simp_rw [tilted_coordinate_product] at h
  rw [weightedGram_coordinate_perturbation, one_mul, det_add_scaled_outer _ hM] at h
  simp only [one_mul, mul_add, mul_one, Finset.sum_add_distrib, tiltedMinorMass_sum] at h
  nlinarith

theorem frame_tiltedMinorMarginal {n k : ℕ} (U : Frame n k)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (i : Fin n) :
    (∑ f : Fin k → Fin n, tiltedMinorMass (frameMatrix U) w f * tupleHit f i) =
      Matrix.det (weightedGram (frameMatrix U) w) * w i *
        (frameMatrix U i ⬝ᵥ ((weightedGram (frameMatrix U) w)⁻¹ *ᵥ frameMatrix U i)) := by
  apply tiltedMinorMarginal
  exact isUnit_iff_ne_zero.mpr (ne_of_gt (frame_weightedGram_posDef U w hw).det_pos)

end CubeSections
