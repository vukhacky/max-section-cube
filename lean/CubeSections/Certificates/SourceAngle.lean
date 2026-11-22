import CubeSections.Certificates.HalfAngle
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
namespace CubeSections.Certificates

/-- Convert the source square-root sine/cosine pair to the rational half-angle coordinate. -/
theorem halfAngle_of_circle {ρ u : ℝ}
    (hρ : 0 < ρ) (hu : 0 < u) (hc : ρ ^ 2 + u ^ 2 = 1) :
    let t := (1 - ρ) / u
    0 < t ∧ t < 1 ∧ sineReal t = u ∧ cosineReal t = ρ := by
  dsimp only
  have hρ₁ : ρ < 1 := by nlinarith [sq_pos_of_pos hu]
  have hsum : 1 < ρ + u := by
    apply (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (by positivity)).mp
    nlinarith [mul_pos hρ hu]
  have ht₀ : 0 < (1 - ρ) / u := div_pos (by linarith) hu
  have ht₁ : (1 - ρ) / u < 1 := (div_lt_one hu).mpr (by linarith)
  have hs : sineReal ((1 - ρ) / u) = u := by
    unfold sineReal
    apply (div_eq_iff (ne_of_gt (halfAngle_denominator_pos ((1 - ρ) / u)))).mpr
    field_simp
    nlinarith
  have hcos : cosineReal ((1 - ρ) / u) = ρ := by
    apply (sq_eq_sq₀ (cosineReal_nonneg ht₀.le ht₁.le) hρ.le).mp
    have hh := halfAngle_circle ((1 - ρ) / u)
    rw [hs] at hh
    nlinarith
  exact ⟨ht₀, ht₁, hs, hcos⟩

/-- The variable s in the manuscript is the squared cosine, not the cosine. -/
theorem halfAngle_of_squared_cosine {s : ℝ} (hs : 0 < s) (hs₁ : s < 1) :
    let t := (1 - Real.sqrt s) / Real.sqrt (1 - s)
    0 < t ∧ t < 1 ∧ sineReal t = Real.sqrt (1 - s) ∧ cosineReal t = Real.sqrt s := by
  apply halfAngle_of_circle (Real.sqrt_pos.mpr hs) (Real.sqrt_pos.mpr (by linarith))
  rw [Real.sq_sqrt hs.le, Real.sq_sqrt (by linarith : 0 ≤ 1 - s)]
  ring

#print axioms halfAngle_of_squared_cosine

end CubeSections.Certificates
