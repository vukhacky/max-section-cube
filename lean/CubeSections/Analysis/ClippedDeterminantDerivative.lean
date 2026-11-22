import CubeSections.LinearAlgebra.MinorEntropy
import CubeSections.LinearAlgebra.WeightedMinorLaw
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Log-determinant differentiation from the finite Cauchy--Binet generating law.
No general Jacobi derivative is assumed. -/

noncomputable section
open scoped BigOperators Matrix

namespace CubeSections

theorem hasDerivAt_determinantRemainder {n k : ℕ} (U : Frame n k)
    (z : ℝ → Fin n → ℝ) (dz : Fin n → ℝ) (t : ℝ)
    (hz : ∀ i, HasDerivAt (fun s => z s i) (dz i) t) :
    HasDerivAt (fun s => determinantRemainder U (z s))
      (∑ i, (Real.exp (z t i) *
        (frameMatrix U i ⬝ᵥ ((weightedGram (frameMatrix U) (fun j => Real.exp (z t j)))⁻¹ *ᵥ
          frameMatrix U i)) - leverage U i) * dz i) t := by
  let w : Fin n → ℝ := fun i => Real.exp (z t i)
  let M := weightedGram (frameMatrix U) w
  let d : ℝ := ∑ f : Fin k → Fin n,
    tupleMinorMass (frameMatrix U) f *
      (Real.exp (tuplePotential f (z t)) * ∑ i, tupleHit f i * dz i)
  have hy (f : Fin k → Fin n) :
      HasDerivAt (fun s => tuplePotential f (z s)) (∑ i, tupleHit f i * dz i) t := by
    unfold tuplePotential
    exact HasDerivAt.fun_sum (fun i _ => (hz i).const_mul (tupleHit f i))
  have hsum : HasDerivAt
      (fun s => ∑ f : Fin k → Fin n,
        tupleMinorMass (frameMatrix U) f * Real.exp (tuplePotential f (z s))) d t := by
    exact HasDerivAt.fun_sum (fun f _ => (hy f).exp.const_mul (tupleMinorMass (frameMatrix U) f))
  have hfun :
      (fun s => Matrix.det (weightedGram (frameMatrix U) (fun i => Real.exp (z s i)))) =
      (fun s => ∑ f : Fin k → Fin n,
        tupleMinorMass (frameMatrix U) f * Real.exp (tuplePotential f (z s))) := by
    funext s
    exact (frame_exp_tuplePotential_mean U (z s)).symm
  have hdet : HasDerivAt
      (fun s => Matrix.det (weightedGram (frameMatrix U) (fun i => Real.exp (z s i)))) d t := by
    rw [hfun]
    exact hsum
  have hmean : HasDerivAt (fun s => ∑ i, leverage U i * z s i)
      (∑ i, leverage U i * dz i) t :=
    HasDerivAt.fun_sum (fun i _ => (hz i).const_mul (leverage U i))
  have hM : M.det ≠ 0 := ne_of_gt (det_weightedGram_exp_pos U (z t))
  have hraw : d = M.det * ∑ i, w i * (frameMatrix U i ⬝ᵥ (M⁻¹ *ᵥ frameMatrix U i)) * dz i := by
    calc
      d = ∑ i, (∑ f : Fin k → Fin n,
          tupleMinorMass (frameMatrix U) f * Real.exp (tuplePotential f (z t)) * tupleHit f i) * dz i := by
        dsimp [d]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro f hf
        ring
      _ = ∑ i, (∑ f : Fin k → Fin n,
          tiltedMinorMass (frameMatrix U) w f * tupleHit f i) * dz i := by
        simp only [weighted_exp_tuplePotential]
        rfl
      _ = ∑ i, (M.det * w i * (frameMatrix U i ⬝ᵥ (M⁻¹ *ᵥ frameMatrix U i))) * dz i := by
        simp only [frame_tiltedMinorMarginal U w (fun i => Real.exp_pos _)]
        rfl
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hder : d / M.det - ∑ i, leverage U i * dz i =
      ∑ i, (w i * (frameMatrix U i ⬝ᵥ (M⁻¹ *ᵥ frameMatrix U i)) - leverage U i) * dz i := by
    rw [hraw]
    simp only [sub_mul, Finset.sum_sub_distrib]
    field_simp
  have h := (hdet.log hM).sub hmean
  rw [show Matrix.det (weightedGram (frameMatrix U) (fun i => Real.exp (z t i))) = M.det from rfl,
    hder] at h
  exact h

end CubeSections
