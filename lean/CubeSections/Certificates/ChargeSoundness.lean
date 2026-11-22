import CubeSections.Certificates.Checker
import CubeSections.Analysis.EntropyEnvelope
import Mathlib.Tactic.Positivity

noncomputable section
namespace CubeSections.Certificates

/-- Real entropy charge for an interacting class, where `j*c<1`. -/
def chargeReal (q j : ℕ) (c : ℝ) : ℝ :=
  entropyExcess q c / (2 * c * (1 - (j : ℝ) * c))

/-- The same rectangle charge envelope as the rational checker. -/
def chargeUpperReal (q j : ℕ) (x X : ℝ) : ℝ :=
  1 / 2 * curvatureEnvelopeReal q (1 - (q : ℝ) * x) *
    (if j = q then 1 else (1 - (q : ℝ) * x) / (1 - (j : ℝ) * x)) *
    (((q : ℝ) + 1) - 1 / X)

theorem curvatureEnvelope_cast (q : ℕ) (z : ℚ) :
    (curvatureEnvelope q z : ℝ) = curvatureEnvelopeReal q (z : ℝ) := by
  simp [curvatureEnvelope, curvatureEnvelopeReal]

theorem chargeUpper_cast (q j : ℕ) (x X : ℚ) :
    (chargeUpper q j x X : ℝ) = chargeUpperReal q j (x : ℝ) (X : ℝ) := by
  unfold chargeUpper chargeUpperReal
  rw [Rat.cast_mul, Rat.cast_mul, Rat.cast_mul, curvatureEnvelope_cast]
  by_cases h : j = q <;> simp [h]

theorem curvatureEnvelopeReal_nonneg (q : ℕ) (hq : 1 ≤ q) (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ curvatureEnvelopeReal q z := by
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have ha₀ : (0 : ℝ) < 1 / ((q : ℝ) + 1) := by positivity
  have ha₁ : (1 : ℝ) / ((q : ℝ) + 1) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  unfold curvatureEnvelopeReal
  dsimp
  positivity

theorem curvatureEnvelopeReal_monotone (q : ℕ) (hq : 1 ≤ q)
    {z Z : ℝ} (hz : 0 ≤ z) (hzZ : z ≤ Z) :
    curvatureEnvelopeReal q z ≤ curvatureEnvelopeReal q Z := by
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  let a : ℝ := 1 / ((q : ℝ) + 1)
  have ha₀ : 0 < a := by dsimp [a]; positivity
  have ha₁ : a < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hZ : 0 ≤ Z := hz.trans hzZ
  have hsq : z ^ 2 ≤ Z ^ 2 := (sq_le_sq₀ hz hZ).mpr hzZ
  have hpoly : a ^ 2 + a * z + z ^ 2 ≤ a ^ 2 + a * Z + Z ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hzZ ha₀.le]
  unfold curvatureEnvelopeReal
  change a / 2 * (1 + (a + z) / 3 + (a ^ 2 + a * z + z ^ 2) / (6 * (1 - a))) ≤
    a / 2 * (1 + (a + Z) / 3 + (a ^ 2 + a * Z + Z ^ 2) / (6 * (1 - a)))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · linarith
  · exact div_le_div_of_nonneg_right hpoly (by positivity)

/-- The real rectangle envelope bounds every nonsingular entropy charge in the box. -/
theorem chargeReal_le_chargeUpperReal (q j : ℕ) (hq : 2 ≤ q)
    (hj₀ : 1 ≤ j) (hjq : j ≤ q) (x X c : ℝ)
    (hx : 1 / ((q : ℝ) + 1) ≤ x) (hX : X ≤ 1 / (q : ℝ))
    (hxc : x ≤ c) (hcX : c ≤ X) (hjc : (j : ℝ) * c < 1) :
    chargeReal q j c ≤ chargeUpperReal q j x X := by
  have hq₂ : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq₀ : (0 : ℝ) < q := by linarith
  have hj₁ : (1 : ℝ) ≤ j := by exact_mod_cast hj₀
  have hjq' : (j : ℝ) ≤ q := by exact_mod_cast hjq
  have ha : (0 : ℝ) < 1 / ((q : ℝ) + 1) := by positivity
  have hx₀ : 0 < x := ha.trans_le hx
  have hc₀ : 0 < c := hx₀.trans_le hxc
  have hX₀ : 0 < X := hc₀.trans_le hcX
  have hqc : (q : ℝ) * c ≤ 1 := by
    have hcb := hcX.trans hX
    have hh := (le_div_iff₀ hq₀).mp hcb
    nlinarith
  have hqx : (q : ℝ) * x ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hxc hq₀.le]
  have hcx : 0 ≤ 1 - (q : ℝ) * c := by linarith
  have hxx : 0 ≤ 1 - (q : ℝ) * x := by linarith
  have hden : 0 < 1 - (j : ℝ) * c := by linarith
  have hdenx : 0 < 1 - (j : ℝ) * x := by
    nlinarith [mul_le_mul_of_nonneg_left hxc (by linarith : (0 : ℝ) ≤ j)]
  have hC : curvatureEnvelopeReal q (1 - (q : ℝ) * c) ≤
      curvatureEnvelopeReal q (1 - (q : ℝ) * x) :=
    curvatureEnvelopeReal_monotone q (by omega) hcx (by nlinarith)
  let B : ℝ → ℝ := fun y => if j = q then 1 else
    (1 - (q : ℝ) * y) / (1 - (j : ℝ) * y)
  have hBc : B c = (1 - (q : ℝ) * c) / (1 - (j : ℝ) * c) := by
    dsimp [B]
    split_ifs with h
    · subst j
      exact (div_self (ne_of_gt hden)).symm
    · rfl
  have hB : B c ≤ B x := by
    dsimp [B]
    split_ifs with h
    · exact le_rfl
    · apply (div_le_div_iff₀ hden hdenx).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hjq') (sub_nonneg.mpr hxc)]
  have hBc₀ : 0 ≤ B c := by rw [hBc]; exact div_nonneg hcx hden.le
  have hBx₀ : 0 ≤ B x := hBc₀.trans hB
  have hDc : 0 ≤ ((q : ℝ) + 1) - 1 / c := by
    have hlow := hx.trans hxc
    have hmul := (div_le_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) + 1)).mp hlow
    have hh : 1 / c ≤ (q : ℝ) + 1 := (div_le_iff₀ hc₀).mpr (by nlinarith)
    linarith
  have hD : ((q : ℝ) + 1) - 1 / c ≤ ((q : ℝ) + 1) - 1 / X := by
    have hi : 1 / X ≤ 1 / c := (one_div_le_one_div hX₀ hc₀).mpr hcX
    linarith
  have hC₀ : 0 ≤ curvatureEnvelopeReal q (1 - (q : ℝ) * c) :=
    curvatureEnvelopeReal_nonneg q (by omega) _ hcx
  have hCX₀ : 0 ≤ curvatureEnvelopeReal q (1 - (q : ℝ) * x) := hC₀.trans hC
  have hEnv := entropyExcess_le_curvatureEnvelope q hq c (hx.trans hxc) (hcX.trans hX)
  have hquot : chargeReal q j c ≤
      (1 - (q : ℝ) * c) * (((q : ℝ) + 1) * c - 1) *
        curvatureEnvelopeReal q (1 - (q : ℝ) * c) / (2 * c * (1 - (j : ℝ) * c)) := by
    exact div_le_div_of_nonneg_right hEnv (by positivity)
  have hrew :
      (1 - (q : ℝ) * c) * (((q : ℝ) + 1) * c - 1) *
        curvatureEnvelopeReal q (1 - (q : ℝ) * c) / (2 * c * (1 - (j : ℝ) * c)) =
      (1 / 2) * curvatureEnvelopeReal q (1 - (q : ℝ) * c) * B c *
        (((q : ℝ) + 1) - 1 / c) := by
    rw [hBc]
    field_simp
    <;> ring
  rw [hrew] at hquot
  unfold chargeUpperReal
  change chargeReal q j c ≤
    1 / 2 * curvatureEnvelopeReal q (1 - (q : ℝ) * x) * B x * (((q : ℝ) + 1) - 1 / X)
  apply hquot.trans
  apply mul_le_mul _ hD hDc (by positivity)
  apply mul_le_mul _ hB hBc₀ (by positivity)
  exact mul_le_mul_of_nonneg_left hC (by norm_num)

#print axioms chargeReal_le_chargeUpperReal

end CubeSections.Certificates
