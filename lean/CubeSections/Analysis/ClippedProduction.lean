import CubeSections.Analysis.ClippedSlopes
import CubeSections.LinearAlgebra.Variance

/-! Pairwise determinant production for every actual frame and every finite real
potential. Continuity and finite-switch monotonicity justify the cutoff argument. -/

noncomputable section
open scoped BigOperators Matrix

namespace CubeSections

theorem determinantRemainder_const {n k : ℕ} (U : Frame n k) (a : ℝ) :
    determinantRemainder U (fun _ => a) = 0 := by
  have hM : weightedGram (frameMatrix U) (fun _ => Real.exp a) =
      Real.exp a • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    simpa only [mul_one, frame_weightedGram_one] using
      weightedGram_const_mul (frameMatrix U) (fun _ => 1) (Real.exp a)
  unfold determinantRemainder
  rw [hM, Matrix.det_smul, Matrix.det_one, mul_one]
  simp only [Fintype.card_fin]
  rw [← Real.exp_mul_natCast, Real.log_exp, ← Finset.sum_mul, sum_leverage]
  ring

theorem gramPairProduction_const {n k : ℕ} (U : Frame n k) (a : ℝ) :
    gramPairProduction U (fun _ => a) = 0 := by
  simp [gramPairProduction, phi]

theorem gramPairProduction_nonneg {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) :
    0 ≤ gramPairProduction U z := by
  unfold gramPairProduction
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (sq_nonneg _) (phi_nonneg _ (abs_nonneg _))

theorem clipped_remainder_difference_monotone {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) :
    Monotone (fun t => determinantRemainder U (clippedPotential z t) -
      gramPairProduction U (clippedPotential z t)) := by
  classical
  let S : Finset ℝ := Finset.univ.image z
  have hne (t : ℝ) (ht : t ∉ S) (i : Fin n) : z i ≠ t := by
    intro hi
    apply ht
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  exact monotone_of_hasDerivAt_nonneg_off_finset S
    ((continuous_clipped_determinantRemainder U z).sub (continuous_clipped_gramPairProduction U z))
    (fun t ht => hasDerivAt_clipped_remainder_difference U z t (hne t ht))
    (fun t _ => clipped_remainder_slope_nonneg U z t)

/-- The manuscript's pairwise determinant lower bound, including zero rows. -/
theorem gramPairProduction_le_determinantRemainder {n k : ℕ} (U : Frame n k) (z : Fin n → ℝ) :
    gramPairProduction U z ≤ determinantRemainder U z := by
  let R : ℝ := ∑ i, |z i|
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => abs_nonneg (z i))
  have hiR (i : Fin n) : |z i| ≤ R :=
    Finset.single_le_sum (fun j _ => abs_nonneg (z j)) (Finset.mem_univ i)
  have hlo (i : Fin n) : -R ≤ z i := by linarith [neg_abs_le (z i), hiR i]
  have hhi (i : Fin n) : z i ≤ R := (le_abs_self (z i)).trans (hiR i)
  have hcliplo : clippedPotential z (-R) = (fun _ => -R) := by
    funext i
    exact min_eq_right (hlo i)
  have hcliphi : clippedPotential z R = z := by
    funext i
    exact min_eq_left (hhi i)
  have h := clipped_remainder_difference_monotone U z (show -R ≤ R by linarith)
  change determinantRemainder U (clippedPotential z (-R)) - gramPairProduction U (clippedPotential z (-R)) ≤
    determinantRemainder U (clippedPotential z R) - gramPairProduction U (clippedPotential z R) at h
  rw [hcliplo, hcliphi, determinantRemainder_const, gramPairProduction_const, sub_self] at h
  exact sub_nonneg.mp h

/-- Exponential production, with the exact scalar constant 9/2. -/
theorem exponential_determinant_production {n k : ℕ} (U : Frame n k)
    (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (9 / 2 : ℝ) * gramVariance U (fun i => Real.exp (-z i / 3)) ≤ determinantRemainder U z := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      mul_le_mul_of_nonneg_left (exponential_pair_production (z i) (z j) (hz i) (hz j))
        (sq_nonneg (gramProjection U i j))))
  have hhalf := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hcoef : (9 / 2 : ℝ) * gramVariance U (fun i => Real.exp (-z i / 3)) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, gramProjection U i j ^ 2 *
        ((9 / 2 : ℝ) * (Real.exp (-z i / 3) - Real.exp (-z j / 3)) ^ 2) := by
    unfold gramVariance
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hcoef]
  exact hhalf.trans (gramPairProduction_le_determinantRemainder U z)

end CubeSections
