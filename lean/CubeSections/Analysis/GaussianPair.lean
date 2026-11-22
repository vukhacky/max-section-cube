import CubeSections.Analysis.GaussianMoments

noncomputable section
open MeasureTheory ProbabilityTheory

namespace CubeSections

theorem integral_gaussianScore_pair (ρ σ : ℝ) (hunit : ρ ^ 2 + σ ^ 2 = 1) :
    (∫ x : ℝ, ∫ y : ℝ, gaussianScore x * gaussianScore (ρ * x + σ * y)
      ∂(gaussianReal 0 1) ∂(gaussianReal 0 1)) = 3 / Real.sqrt (16 - ρ ^ 2) := by
  have hσ : 0 < 3 + σ ^ 2 := by positivity
  have hρ : 0 < 16 - ρ ^ 2 := by nlinarith [sq_nonneg σ]
  let a : ℝ := 1 / 6 + ρ ^ 2 / (2 * (3 + σ ^ 2))
  have ha₀ : 0 ≤ a := by dsimp [a]; positivity
  have ha : 0 < 1 + 2 * a := by positivity
  have hinner (x : ℝ) :
      (∫ y : ℝ, gaussianScore x * gaussianScore (ρ * x + σ * y) ∂(gaussianReal 0 1)) =
        Real.sqrt (3 / (3 + σ ^ 2)) * Real.exp (-a * x ^ 2) := by
    rw [integral_const_mul, integral_gaussianScore_affine]
    unfold gaussianScore
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    dsimp [a]
    ring
  simp_rw [hinner]
  rw [integral_const_mul]
  have hout : (∫ x : ℝ, Real.exp (-a * x ^ 2) ∂(gaussianReal 0 1)) =
      Real.sqrt (1 / (1 + 2 * a)) := by
    simpa using integral_standardGaussian_quadratic a 0 0 ha
  rw [hout, ← Real.sqrt_mul (by positivity : 0 ≤ 3 / (3 + σ ^ 2))]
  have hden : (3 + σ ^ 2) * (1 + 2 * a) = (16 - ρ ^ 2) / 3 := by
    calc
      _ = (4 * (3 + σ ^ 2) + 3 * ρ ^ 2) / 3 := by
        dsimp [a]
        field_simp
        ring
      _ = _ := by congr 1; nlinarith [hunit]
  have hfrac : 3 / (3 + σ ^ 2) * (1 / (1 + 2 * a)) = 9 / (16 - ρ ^ 2) := by
    rw [div_mul_div_comm, mul_one, hden]
    field_simp
    ring
  rw [hfrac, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 9)]
  rw [show Real.sqrt (9 : ℝ) = 3 from
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)]

end CubeSections
