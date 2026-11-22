import CubeSections.LinearAlgebra.MinorLaw
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! The log-determinant remainder is the cumulant remainder of the genuine
Cauchy--Binet law, including zero rows and zero minors. -/
noncomputable section
open scoped BigOperators Matrix
namespace CubeSections

def tuplePotential {n k : ℕ} (f : Fin k → Fin n) (z : Fin n → ℝ) : ℝ :=
  ∑ i, tupleHit f i * z i

theorem tuplePotential_of_injective {n k : ℕ} (f : Fin k → Fin n)
    (hf : Function.Injective f) (z : Fin n → ℝ) :
    tuplePotential f z = ∑ a, z (f a) := by
  classical
  have hs : Finset.univ.filter (fun i => ∃ a, f a = i) = Finset.univ.image f := by
    ext i
    simp
  unfold tuplePotential
  have hp (i : Fin n) : tupleHit f i * z i = if ∃ a, f a = i then z i else 0 := by
    unfold tupleHit
    split_ifs <;> simp
  simp_rw [hp]
  rw [← Finset.sum_filter, hs, Finset.sum_image]
  intro a ha b hb hab
  exact hf hab

theorem frame_tuplePotential_mean {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) :
    (∑ f : Fin k → Fin n, tupleMinorMass (frameMatrix U) f * tuplePotential f z) =
      ∑ i, leverage U i * z i := by
  simp only [tuplePotential, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [← mul_assoc, ← Finset.sum_mul]
  rw [show (∑ f : Fin k → Fin n, tupleMinorMass (frameMatrix U) f * tupleHit f i) =
    leverage U i from frame_tupleMarginal U i]

theorem weighted_exp_tuplePotential {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (f : Fin k → Fin n) (z : Fin n → ℝ) :
    tupleMinorMass A f * Real.exp (tuplePotential f z) =
      tupleMinorMass A f * ∏ a, Real.exp (z (f a)) := by
  classical
  by_cases hf : Function.Injective f
  · rw [tuplePotential_of_injective f hf, Real.exp_sum]
  · simp [tupleMinorMass_eq_zero_of_not_injective A f hf]

theorem frame_exp_tuplePotential_mean {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) :
    (∑ f : Fin k → Fin n, tupleMinorMass (frameMatrix U) f * Real.exp (tuplePotential f z)) =
      Matrix.det (weightedGram (frameMatrix U) (fun i => Real.exp (z i))) := by
  simp_rw [weighted_exp_tuplePotential]
  exact tupleMinor_generating (frameMatrix U) (fun i : Fin n => Real.exp (z i))

theorem exp_le_det_weightedGram {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) :
    Real.exp (∑ i, leverage U i * z i) ≤
      Matrix.det (weightedGram (frameMatrix U) (fun i => Real.exp (z i))) := by
  have h := convexOn_exp.map_sum_le
    (t := Finset.univ)
    (w := fun f : Fin k → Fin n => tupleMinorMass (frameMatrix U) f)
    (p := fun f => tuplePotential f z)
    (fun f _ => tupleMinorMass_nonneg _ f)
    (frame_tupleMinorMass_sum U) (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at h
  rw [frame_tuplePotential_mean, frame_exp_tuplePotential_mean] at h
  exact h

theorem det_weightedGram_exp_pos {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) :
    0 < Matrix.det (weightedGram (frameMatrix U) (fun i => Real.exp (z i))) :=
  (Real.exp_pos _).trans_le (exp_le_det_weightedGram U z)

def determinantRemainder {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) : ℝ :=
  Real.log (Matrix.det (weightedGram (frameMatrix U) (fun i => Real.exp (z i)))) -
    ∑ i, leverage U i * z i

theorem determinantRemainder_eq_tuple_cumulant {n k : ℕ}
    (U : Frame n k) (z : Fin n → ℝ) :
    determinantRemainder U z =
      Real.log (∑ f : Fin k → Fin n,
        tupleMinorMass (frameMatrix U) f * Real.exp (tuplePotential f z)) -
      ∑ f : Fin k → Fin n, tupleMinorMass (frameMatrix U) f * tuplePotential f z := by
  rw [frame_exp_tuplePotential_mean, frame_tuplePotential_mean]
  rfl

theorem determinantRemainder_nonneg {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) :
    0 ≤ determinantRemainder U z := by
  have h := Real.log_le_log (Real.exp_pos _) (exp_le_det_weightedGram U z)
  rw [Real.log_exp] at h
  exact sub_nonneg.mpr h

end CubeSections
