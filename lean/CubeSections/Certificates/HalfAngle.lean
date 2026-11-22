import CubeSections.Certificates.Checker
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

namespace CubeSections.Certificates

def sineReal (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)
def cosineReal (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)

theorem sine_cast (t : ℚ) : (sine t : ℝ) = sineReal (t : ℝ) := by
  simp [sine, sineReal]

theorem cosine_cast (t : ℚ) : (cosine t : ℝ) = cosineReal (t : ℝ) := by
  simp [cosine, cosineReal]

theorem halfAngle_denominator_pos (t : ℝ) : 0 < 1 + t ^ 2 := by
  positivity

theorem sineReal_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ sineReal t := by
  unfold sineReal
  positivity

theorem sineReal_le_one (t : ℝ) : sineReal t ≤ 1 := by
  apply (div_le_iff₀ (halfAngle_denominator_pos t)).mpr
  nlinarith [sq_nonneg (t - 1)]

theorem cosineReal_nonneg {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ cosineReal t := by
  unfold cosineReal
  apply div_nonneg _ (halfAngle_denominator_pos t).le
  nlinarith

theorem cosineReal_le_one (t : ℝ) : cosineReal t ≤ 1 := by
  apply (div_le_iff₀ (halfAngle_denominator_pos t)).mpr
  nlinarith [sq_nonneg t]

theorem halfAngle_circle (t : ℝ) : sineReal t ^ 2 + cosineReal t ^ 2 = 1 := by
  unfold sineReal cosineReal
  field_simp
  <;> ring

theorem sineReal_le_twice {t : ℝ} (ht : 0 ≤ t) : sineReal t ≤ 2 * t := by
  apply (div_le_iff₀ (halfAngle_denominator_pos t)).mpr
  nlinarith [mul_nonneg ht (sq_nonneg t)]

theorem sineReal_monotoneOn : MonotoneOn sineReal (Set.Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  apply (div_le_div_iff₀ (halfAngle_denominator_pos s) (halfAngle_denominator_pos t)).mpr
  have hprod : s * t ≤ 1 := calc
    s * t ≤ 1 * t := mul_le_mul_of_nonneg_right hs.2 ht.1
    _ ≤ 1 := by simpa using ht.2
  have hnonneg := mul_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr hprod)
  nlinarith

theorem cosineReal_antitoneOn : AntitoneOn cosineReal (Set.Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  apply (div_le_div_iff₀ (halfAngle_denominator_pos t) (halfAngle_denominator_pos s)).mpr
  have hsq : s ^ 2 ≤ t ^ 2 := (sq_le_sq₀ hs.1 ht.1).mpr hst
  nlinarith

theorem halfAngle_cross_le_one (t : ℝ) : 2 * sineReal t * cosineReal t ≤ 1 := by
  nlinarith [halfAngle_circle t, sq_nonneg (sineReal t - cosineReal t)]

theorem halfAngle_sum_le_two (t : ℝ) :
    sineReal t + 2 * sineReal t * cosineReal t ≤ 2 := by
  linarith [sineReal_le_one t, halfAngle_cross_le_one t]

/-- Exact derivative of the rational half-angle sine. -/
theorem hasDerivAt_sineReal (t : ℝ) :
    HasDerivAt sineReal (2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2) t := by
  have h := ((hasDerivAt_id t).const_mul (2 : ℝ)).div
    ((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).pow 2))
    (ne_of_gt (halfAngle_denominator_pos t))
  convert h using 1
  · rfl
  · dsimp
    ring

def stripProfile (η t : ℝ) : ℝ := t * (1 - η * sineReal t) ^ 2

/-- Factorization of the derivative used in the source's strip exclusion. -/
theorem hasDerivAt_stripProfile (η t : ℝ) :
    HasDerivAt (stripProfile η)
      ((1 - η * sineReal t) *
        (1 - η * (sineReal t + 2 * sineReal t * cosineReal t))) t := by
  have h := (hasDerivAt_id t).mul
    (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_sineReal t).const_mul η)).pow 2)
  convert h using 1
  · rfl
  · dsimp [sineReal, cosineReal]
    field_simp
    <;> ring

theorem stripProfile_derivative_nonneg {η t : ℝ}
    (hη : 0 ≤ η) (hη1 : η ≤ 1 / 2) :
    0 ≤ (1 - η * sineReal t) *
      (1 - η * (sineReal t + 2 * sineReal t * cosineReal t)) := by
  have hfirst : η * sineReal t ≤ η := by
    simpa using mul_le_mul_of_nonneg_left (sineReal_le_one t) hη
  have hsecond : η * (sineReal t + 2 * sineReal t * cosineReal t) ≤ 2 * η := by
    nlinarith [mul_le_mul_of_nonneg_left (halfAngle_sum_le_two t) hη]
  exact mul_nonneg (by linarith) (by linarith)

/-- In fact the derivative argument proves global monotonicity for 0≤η≤1/2. -/
theorem stripProfile_monotone {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1 / 2) :
    Monotone (stripProfile η) := by
  apply monotone_of_hasDerivAt_nonneg (hasDerivAt_stripProfile η)
  intro t
  exact stripProfile_derivative_nonneg hη hη1

#print axioms sineReal_monotoneOn
#print axioms stripProfile_monotone

end CubeSections.Certificates
