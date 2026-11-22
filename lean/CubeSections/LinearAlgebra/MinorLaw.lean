import CubeSections.LinearAlgebra.CauchyBinet
import CubeSections.LinearAlgebra.RankUpdate

/-! Exact first and second inclusion marginals of the Cauchy--Binet tuple law. -/
noncomputable section
open scoped BigOperators Matrix
namespace CubeSections

def tupleHit {n k : ℕ} (f : Fin k → Fin n) (i : Fin n) : ℝ :=
  if ∃ a, f a = i then 1 else 0

def coordinateWeight {n : ℕ} (i : Fin n) (x : ℝ) (b : Fin n) : ℝ :=
  1 + if b = i then x else 0

theorem tupleHit_nonneg {n k : ℕ} (f : Fin k → Fin n) (i : Fin n) :
    0 ≤ tupleHit f i := by unfold tupleHit; split_ifs <;> norm_num

theorem tupleHit_sq {n k : ℕ} (f : Fin k → Fin n) (i : Fin n) :
    tupleHit f i ^ 2 = tupleHit f i := by unfold tupleHit; split_ifs <;> norm_num

theorem prod_coordinateWeight_of_injective {n k : ℕ}
    (f : Fin k → Fin n) (hf : Function.Injective f) (i : Fin n) (x : ℝ) :
    (∏ a, coordinateWeight i x (f a)) = 1 + x * tupleHit f i := by
  classical
  by_cases h : ∃ a, f a = i
  · obtain ⟨a, ha⟩ := h
    have hex : ∃ b, f b = i := ⟨a, ha⟩
    have heq (b : Fin k) : f b = i ↔ b = a := by rw [← ha, hf.eq_iff]
    have hpoint (b : Fin k) : 1 + (if b = a then x else 0) =
        if b = a then 1 + x else 1 := by split_ifs <;> simp
    simp only [coordinateWeight, heq, hpoint]
    simp [tupleHit, hex]
  · have hn (a : Fin k) : f a ≠ i := by intro ha; exact h ⟨a, ha⟩
    simp [coordinateWeight, hn, tupleHit, h]

theorem weightedGram_coordinateWeight {n k : ℕ}
    (A : Matrix (Fin n) (Fin k) ℝ) (i : Fin n) (x : ℝ) :
    weightedGram A (coordinateWeight i x) =
      A.transpose * A + x • Matrix.vecMulVec (A i) (A i) := by
  ext a b
  change weightedGram A (coordinateWeight i x) a b =
    (A.transpose * A) a b + x * (A i a * A i b)
  rw [weightedGram_apply, Matrix.mul_apply]
  simp [coordinateWeight, Matrix.transpose_apply, mul_add, add_mul,
    Finset.sum_add_distrib, mul_ite, ite_mul, mul_assoc, mul_left_comm]

def tupleMarginal {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (i : Fin n) : ℝ :=
  ∑ f : Fin k → Fin n, tupleMinorMass A f * tupleHit f i

def tuplePairMarginal {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (i j : Fin n) : ℝ :=
  ∑ f : Fin k → Fin n, tupleMinorMass A f * tupleHit f i * tupleHit f j

theorem weighted_coordinate_product {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (f : Fin k → Fin n) (i : Fin n) (x : ℝ) :
    tupleMinorMass A f * (∏ a, coordinateWeight i x (f a)) =
      tupleMinorMass A f * (1 + x * tupleHit f i) := by
  classical
  by_cases hf : Function.Injective f
  · rw [prod_coordinateWeight_of_injective f hf]
  · simp [tupleMinorMass_eq_zero_of_not_injective A f hf]

theorem frame_tupleMarginal {n k : ℕ} (U : Frame n k) (i : Fin n) :
    tupleMarginal (frameMatrix U) i = leverage U i := by
  have h := tupleMinor_generating (frameMatrix U) (coordinateWeight i 1)
  simp_rw [weighted_coordinate_product] at h
  rw [weightedGram_coordinateWeight, frameMatrix_transpose_mul, one_smul,
    det_duplicate_row] at h
  have hexp : (∑ f : Fin k → Fin n,
      tupleMinorMass (frameMatrix U) f * (1 + 1 * tupleHit f i)) =
      1 + tupleMarginal (frameMatrix U) i := by
    simp only [one_mul, mul_add, mul_one, Finset.sum_add_distrib,
      frame_tupleMinorMass_sum, tupleMarginal]
  rw [hexp] at h
  linarith

theorem coordinateWeight_pair {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x y : ℝ) :
    (fun b => coordinateWeight i x b * coordinateWeight j y b) =
      fun b => 1 + (if b = i then x else 0) + (if b = j then y else 0) := by
  funext b
  by_cases hi : b = i
  · subst b
    simp [coordinateWeight, hij]
  · by_cases hj : b = j
    · subst b
      simp [coordinateWeight, hi]
    · simp [coordinateWeight, hi, hj]

theorem weightedGram_pair {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (i j : Fin n) (hij : i ≠ j) (x y : ℝ) :
    weightedGram A (fun b => coordinateWeight i x b * coordinateWeight j y b) =
      A.transpose * A + x • Matrix.vecMulVec (A i) (A i) +
        y • Matrix.vecMulVec (A j) (A j) := by
  rw [coordinateWeight_pair i j hij]
  ext a b
  change weightedGram A (fun t => 1 + (if t = i then x else 0) +
    (if t = j then y else 0)) a b =
      (A.transpose * A) a b + x * (A i a * A i b) + y * (A j a * A j b)
  rw [weightedGram_apply, Matrix.mul_apply]
  simp [Matrix.transpose_apply, mul_add, add_mul, Finset.sum_add_distrib,
    mul_ite, ite_mul, mul_assoc, mul_left_comm]

theorem weighted_coordinate_pair_product {n k : ℕ}
    (A : Matrix (Fin n) (Fin k) ℝ) (f : Fin k → Fin n)
    (i j : Fin n) (x y : ℝ) :
    tupleMinorMass A f * (∏ a, coordinateWeight i x (f a) * coordinateWeight j y (f a)) =
      tupleMinorMass A f * (1 + x * tupleHit f i) * (1 + y * tupleHit f j) := by
  classical
  by_cases hf : Function.Injective f
  · rw [Finset.prod_mul_distrib, prod_coordinateWeight_of_injective f hf,
      prod_coordinateWeight_of_injective f hf]
    ring
  · simp [tupleMinorMass_eq_zero_of_not_injective A f hf]

theorem frame_tuplePairMarginal {n k : ℕ} (U : Frame n k) (i j : Fin n) (hij : i ≠ j) :
    tuplePairMarginal (frameMatrix U) i j =
      leverage U i * leverage U j - gramProjection U i j ^ 2 := by
  have h := tupleMinor_generating (frameMatrix U)
    (fun b => coordinateWeight i 1 b * coordinateWeight j 1 b)
  simp_rw [weighted_coordinate_pair_product] at h
  rw [weightedGram_pair _ i j hij, frameMatrix_transpose_mul,
    det_one_add_two_scaled_outer] at h
  have hdot (a b : Fin n) :
      (frameMatrix U a) ⬝ᵥ (frameMatrix U b) = gramProjection U a b := rfl
  simp only [hdot, one_mul, mul_one] at h
  have hexp : (∑ f : Fin k → Fin n, tupleMinorMass (frameMatrix U) f *
      (1 + tupleHit f i) * (1 + tupleHit f j)) =
      1 + tupleMarginal (frameMatrix U) i + tupleMarginal (frameMatrix U) j +
        tuplePairMarginal (frameMatrix U) i j := by
    have hp (f : Fin k → Fin n) : tupleMinorMass (frameMatrix U) f *
        (1 + tupleHit f i) * (1 + tupleHit f j) =
        tupleMinorMass (frameMatrix U) f + tupleMinorMass (frameMatrix U) f * tupleHit f i +
        tupleMinorMass (frameMatrix U) f * tupleHit f j +
        tupleMinorMass (frameMatrix U) f * tupleHit f i * tupleHit f j := by ring
    simp only [hp, Finset.sum_add_distrib, frame_tupleMinorMass_sum,
      tupleMarginal, tuplePairMarginal]
  rw [hexp, frame_tupleMarginal, frame_tupleMarginal] at h
  change 1 + leverage U i + leverage U j + tuplePairMarginal (frameMatrix U) i j =
    (1 + leverage U i) * (1 + leverage U j) - gramProjection U i j ^ 2 at h
  nlinarith

end CubeSections
