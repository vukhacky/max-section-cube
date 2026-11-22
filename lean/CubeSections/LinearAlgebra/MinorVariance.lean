import CubeSections.LinearAlgebra.MinorEntropy
import CubeSections.LinearAlgebra.Variance

/-! The variance of the Cauchy--Binet statistic is the actual Gram pair form. -/
noncomputable section
open scoped BigOperators
namespace CubeSections

theorem tuplePairMarginal_self {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (i : Fin n) :
    tuplePairMarginal A i i = tupleMarginal A i := by
  unfold tuplePairMarginal tupleMarginal
  apply Finset.sum_congr rfl
  intro f hf
  rw [mul_assoc, ← pow_two, tupleHit_sq]

theorem frame_tuplePairMarginal_all {n k : ℕ} (U : Frame n k) (i j : Fin n) :
    tuplePairMarginal (frameMatrix U) i j =
      leverage U i * leverage U j - gramProjection U i j ^ 2 +
        if i = j then leverage U i else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [tuplePairMarginal_self, frame_tupleMarginal]
    simp only [ite_true]
    change leverage U i = leverage U i * leverage U i - leverage U i ^ 2 + leverage U i
    ring
  · simp only [hij, ite_false, add_zero, frame_tuplePairMarginal U i j hij]

theorem tuplePotential_sq_expansion {n k : ℕ} (f : Fin k → Fin n) (z : Fin n → ℝ) :
    tuplePotential f z ^ 2 = ∑ i, ∑ j, tupleHit f i * tupleHit f j * z i * z j := by
  unfold tuplePotential
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem frame_tuplePotential_secondMoment {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) :
    (∑ f : Fin k → Fin n, tupleMinorMass (frameMatrix U) f * tuplePotential f z ^ 2) =
      (∑ i, leverage U i * z i) ^ 2 + gramVariance U z := by
  classical
  have hexp : (∑ f : Fin k → Fin n,
      tupleMinorMass (frameMatrix U) f * tuplePotential f z ^ 2) =
      ∑ i, ∑ j, tuplePairMarginal (frameMatrix U) i j * z i * z j := by
    simp only [tuplePotential_sq_expansion, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    unfold tuplePairMarginal
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro f hf
    ring
  rw [hexp]
  simp_rw [frame_tuplePairMarginal_all]
  have hp (i j : Fin n) :
      (leverage U i * leverage U j - gramProjection U i j ^ 2 +
          if i = j then leverage U i else 0) * z i * z j =
        (leverage U i * z i) * (leverage U j * z j) -
          gramProjection U i j ^ 2 * z i * z j +
          if i = j then leverage U i * z i ^ 2 else 0 := by
    split_ifs with h
    · subst j; ring
    · ring
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [gramVariance_identity]
  unfold gramSchurForm
  have hprod : (∑ i, ∑ j, (leverage U i * z i) * (leverage U j * z j)) =
      (∑ i, leverage U i * z i) ^ 2 := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  rw [hprod]
  ring

def tupleVariance {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) : ℝ :=
  ∑ f : Fin k → Fin n, tupleMinorMass (frameMatrix U) f *
    (tuplePotential f z - ∑ i, leverage U i * z i) ^ 2

theorem tupleVariance_eq_gramVariance {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) :
    tupleVariance U z = gramVariance U z := by
  let m := ∑ i, leverage U i * z i
  have hp (f : Fin k → Fin n) :
      tupleMinorMass (frameMatrix U) f * (tuplePotential f z - m) ^ 2 =
        tupleMinorMass (frameMatrix U) f * tuplePotential f z ^ 2 -
          2 * m * (tupleMinorMass (frameMatrix U) f * tuplePotential f z) +
          m ^ 2 * tupleMinorMass (frameMatrix U) f := by ring
  change (∑ f : Fin k → Fin n,
    tupleMinorMass (frameMatrix U) f * (tuplePotential f z - m) ^ 2) = _
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [frame_tuplePotential_secondMoment, frame_tuplePotential_mean, frame_tupleMinorMass_sum]
  dsimp [m]
  ring

end CubeSections
