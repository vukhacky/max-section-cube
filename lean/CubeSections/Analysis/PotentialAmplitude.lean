import CubeSections.Analysis.GlobalScoreEnergy

/-! Normalized width potentials and the global pointwise score-energy inequality. -/

noncomputable section
open scoped BigOperators

namespace CubeSections

theorem pairAmplitude_exp (β η : ℝ) :
    pairAmplitude (Real.exp (2 * β / 3)) (Real.exp (2 * η / 3)) =
      Real.exp (-(β - min β η) / 3) := by
  have hmin : min (Real.exp (2 * β / 3)) (Real.exp (2 * η / 3)) =
      Real.exp (2 * min β η / 3) := by
    rcases le_total β η with h | h
    · rw [min_eq_left h, min_eq_left (Real.exp_le_exp.mpr (by linarith))]
    · rw [min_eq_right h, min_eq_right (Real.exp_le_exp.mpr (by linarith))]
  rw [pairAmplitude, hmin, ← Real.exp_sub]
  apply (Real.sqrt_eq_iff_eq_sq (Real.exp_pos _).le (Real.exp_pos _).le).mpr
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem normalized_potential_pair_production (β η T S : ℝ) :
    (pairAmplitude (Real.exp (2 * β / 3)) (Real.exp (2 * η / 3)) * gaussianScore T -
      pairAmplitude (Real.exp (2 * η / 3)) (Real.exp (2 * β / 3)) * gaussianScore S) ^ 2 ≤
      (2 / 9 : ℝ) * phi |(β + T ^ 2 / 2) - (η + S ^ 2 / 2)| := by
  let m : ℝ := min β η
  let x : ℝ := β - m + T ^ 2 / 2
  let y : ℝ := η - m + S ^ 2 / 2
  have hx : 0 ≤ x := by dsimp [x, m]; nlinarith [min_le_left β η, sq_nonneg T]
  have hy : 0 ≤ y := by dsimp [y, m]; nlinarith [min_le_right β η, sq_nonneg S]
  have h := exponential_pair_production x y hx hy
  have hdiff : x - y = (β + T ^ 2 / 2) - (η + S ^ 2 / 2) := by dsimp [x, y]; ring
  rw [hdiff] at h
  have hprod (d t : ℝ) : Real.exp (-(d - m) / 3) * gaussianScore t =
      Real.exp (-(d - m + t ^ 2 / 2) / 3) := by
    unfold gaussianScore
    rw [← Real.exp_add]
    congr 1
    ring
  rw [pairAmplitude_exp, pairAmplitude_exp, min_comm η β]
  change (Real.exp (-(β - m) / 3) * gaussianScore T -
    Real.exp (-(η - m) / 3) * gaussianScore S) ^ 2 ≤ _
  rw [hprod, hprod]
  change (Real.exp (-x / 3) - Real.exp (-y / 3)) ^ 2 ≤ _
  nlinarith

theorem potential_score_transfer {n k : ℕ} (U : Frame n k)
    (β T G : Fin n → ℝ) :
    amplitudeVariance U (fun i => Real.exp (2 * β i / 3)) (fun i => gaussianScore (G i)) ≤
      (2 / 9 + 2 / (3 * Real.exp 1)) *
        ((1 / 2 : ℝ) * ∑ i, ∑ j, gramProjection U i j ^ 2 *
          phi |(β i + T i ^ 2 / 2) - (β j + T j ^ 2 / 2)| +
          (1 / 2 : ℝ) * ∑ i, leverage U i * (T i - G i) ^ 2) := by
  exact global_score_transfer U (fun i => Real.exp (2 * β i / 3)) T G
    (fun i j => phi |(β i + T i ^ 2 / 2) - (β j + T j ^ 2 / 2)|)
    (fun i => Real.exp_pos _) (fun i j => normalized_potential_pair_production _ _ _ _)

end CubeSections
