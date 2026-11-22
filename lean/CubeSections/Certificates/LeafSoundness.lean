import CubeSections.Certificates.RectangleBounds
import CubeSections.Certificates.StripSoundness
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
namespace CubeSections.Certificates

/-- Source geometric constraints; no desired comparison is included as a hypothesis. -/
structure FeasiblePair (p : Parameters) (c d R t : ℝ) : Prop where
  angle_pos : 0 < t
  angle_lt_one : t < 1
  first_class : (p.m : ℝ) * c < 1
  second_class : (p.l : ℝ) * d < 1
  complementary : cosineReal t ^ 2 ≤
    (1 - (p.m : ℝ) * c) * (1 - (p.l : ℝ) * d) /
      (((p.m : ℝ) * c) * ((p.l : ℝ) * d))
  radius_lower : 1 / (p.q : ℝ) ≤ R
  radius_upper : R ≤ (radiusUpper p : ℝ)
  strip : DirectStripLaw (determinantReal c d t) R (scaleReal c d R t) t (c * d)

/-- Real incidence cost from the source, using the squared cosine. -/
def pairAngularCost (A B s : ℝ) : ℝ :=
  Real.sqrt (3 / 5) * (1 - s) /
    ((16 - s) * (2 / 9 + (2 / (3 * Real.exp 1)) * (2 - A - B)))

theorem Parameters.two_le_q {p : Parameters} (hp : p.Valid) : 2 ≤ p.q := by
  rcases hp.1 with h | h | h <;> omega

theorem charges_le_sum {p : Parameters} {r : Rectangle}
    (hp : p.Valid) (hr : r.InWindow p.q) {c d : ℝ}
    (hcd : r.Contains c d) (hc : (p.m : ℝ) * c < 1) (hd : (p.l : ℝ) * d < 1) :
    chargeReal p.q p.m c + chargeReal p.q p.l d + (1 : ℝ) / 4000 ≤
      (chargeSum p r : ℝ) := by
  have hx : 1 / ((p.q : ℝ) + 1) ≤ (r.lowerC : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hr.1
  have hX : (r.upperC : ℝ) ≤ 1 / (p.q : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hr.2.2.1
  have hy : 1 / ((p.q : ℝ) + 1) ≤ (r.lowerD : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hr.2.2.2.1
  have hY : (r.upperD : ℝ) ≤ 1 / (p.q : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hr.2.2.2.2.2
  have hc' := chargeReal_le_chargeUpperReal p.q p.m (Parameters.two_le_q hp) hp.2.1
    (hp.2.2.1.trans hp.2.2.2) _ _ _ hx hX hcd.1 hcd.2.1 hc
  have hd' := chargeReal_le_chargeUpperReal p.q p.l (Parameters.two_le_q hp)
    (hp.2.1.trans hp.2.2.1) hp.2.2.2 _ _ _ hy hY hcd.2.2.1 hcd.2.2.2 hd
  simpa [chargeSum, chargeUpper_cast, surplus] using
    add_le_add_right (add_le_add hc' hd') ((1 : ℝ) / 4000)

theorem projectionLower_le_sine_sq {p : Parameters} {r : Rectangle}
    (hp : p.Valid) (hr : r.InWindow p.q) {c d R t : ℝ}
    (hcd : r.Contains c d) (hf : FeasiblePair p c d R t) :
    (projectionLower p r : ℝ) ≤ sineReal t ^ 2 := by
  have hq := Parameters.two_le_q hp
  obtain ⟨hx, hy⟩ := Rectangle.lower_pos (by omega : 1 ≤ p.q) hr
  have hm : (0 : ℝ) < p.m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp.2.1)
  have hl : (0 : ℝ) < p.l := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hp.2.1.trans hp.2.2.1))
  have hh := complementary_projection_bound
    (mul_pos hm hx) (mul_pos hl hy)
    (mul_le_mul_of_nonneg_left hcd.1 hm.le)
    (mul_le_mul_of_nonneg_left hcd.2.2.1 hl.le)
    hf.first_class.le hf.second_class.le hf.complementary
  have hden : (p.m : ℝ) * p.l * (r.lowerC : ℝ) * (r.lowerD : ℝ) =
      ((p.m : ℝ) * (r.lowerC : ℝ)) * ((p.l : ℝ) * (r.lowerD : ℝ)) := by ring
  simp only [projectionLower, Rat.cast_max, Rat.cast_zero, Rat.cast_sub, Rat.cast_one,
    Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
  rw [hden]
  apply max_le (sq_nonneg _) _
  nlinarith [halfAngle_circle t]

/-- A successful leaf gives the coarse angular comparison throughout its real box. -/
theorem Leaf.angular_sound {p : Parameters} {r : Rectangle} {a : Leaf}
    (ha : a.Accepts p r) {c d R t : ℝ} (hcd : r.Contains c d)
    (hf : FeasiblePair p c d R t) :
    (chargeSum p r : ℝ) < Real.sqrt (3 / 5) * sineReal t ^ 2 /
      ((15 + sineReal t ^ 2) * (angularDenominator p r : ℝ)) := by
  cases a with
  | projection =>
      rcases ha with ⟨hp, hr, hS, hK, ht⟩
      exact ht.sound_of_le hS.le hK (le_max_left _ _) (projectionLower_le_sine_sq hp hr hcd hf)
  | strip T =>
      rcases ha with ⟨hp, hr, hS, hK, hT₀, hT₁, hthreshold, hB, hA, hη₀, hη₁, htest⟩
      have hq : 2 ≤ p.q := (Parameters.two_le_q hp)
      have hq' : (2 : ℝ) ≤ p.q := by exact_mod_cast hq
      have hT₀' : (0 : ℝ) ≤ T := by exact_mod_cast hT₀
      have hT₁' : (T : ℝ) ≤ 1 := by exact_mod_cast hT₁
      by_cases htT : t ≤ (T : ℝ)
      · have hb : (0 : ℝ) < 1 / (p.q : ℝ) := by positivity
        have hR : 0 < R := hb.trans_le hf.radius_lower
        have hA' : (0 : ℝ) < determinantLower r T := by exact_mod_cast hA
        have hη₀' : (0 : ℝ) ≤ eta p r T := by exact_mod_cast hη₀
        have hAL := Rectangle.determinantLower_le (by omega : 1 ≤ p.q) hr hcd
          hf.angle_pos.le htT hT₁'
        have hL : 0 ≤ determinantReal c d t := hA'.le.trans hAL
        obtain ⟨hc₀, hcb, hd₀, hdb⟩ := Rectangle.point_bounds hr hcd
        have hlow : (0 : ℝ) < 1 / ((p.q : ℝ) + 1) := by positivity
        have hcpos := hlow.trans_le hc₀
        have hdpos := hlow.trans_le hd₀
        obtain ⟨hα₀, hα₁⟩ := scaleReal_mem hq hcpos.le hdpos.le hcb hdb hf.radius_lower hL
        have hηα := Rectangle.eta_le_scale (by omega : 1 ≤ p.q) hr hcd
          hf.angle_pos.le htT hT₁' hA'.le hR hf.radius_upper
        obtain ⟨hD, hDC⟩ := Rectangle.product_upper (by omega : 1 ≤ p.q) hr hcd
        have htest' :
            2 * (radiusUpper p : ℝ) * (T : ℝ) *
              (1 + (r.upperC : ℝ) * (r.upperD : ℝ) * sineReal (T : ℝ) ^ 2 / 4) *
              (1 - (eta p r T : ℝ) * sineReal (T : ℝ)) ^ 2 <
            (determinantLower r T : ℝ) ^ 2 := by
          have hh := (Rat.cast_lt (K := ℝ)).mpr htest
          simpa [sine_cast] using hh
        exact False.elim (directStripLaw_excluded hA'.le hAL hR hf.radius_upper hα₀ hα₁
          hη₀' hηα hf.angle_pos.le htT hT₁' hD.le hDC hf.strip htest')
      · have hTt : (T : ℝ) < t := lt_of_not_ge htT
        have htestT : AngleTest (chargeSum p r) (angularDenominator p r) (sine T ^ 2) := by
          rcases hthreshold with h | h
          · have hreal : (T : ℝ) = 1 := by exact_mod_cast h
            linarith [hf.angle_lt_one]
          · exact h
        have hsin : sineReal (T : ℝ) ≤ sineReal t :=
          sineReal_monotoneOn ⟨hT₀', hT₁'⟩ ⟨hf.angle_pos.le, hf.angle_lt_one.le⟩ hTt.le
        apply htestT.sound_of_le hS.le hK (sq_nonneg _)
        simpa only [Rat.cast_pow, sine_cast] using
          (sq_le_sq₀ (sineReal_nonneg hT₀') (sineReal_nonneg hf.angle_pos.le)).mpr hsin

/-- The denominator envelope retains the source exponential constant. -/
theorem coarse_angular_le_cost {p : Parameters} {r : Rectangle}
    (hp : p.Valid) (hr : r.InWindow p.q) {c d R t : ℝ}
    (hcd : r.Contains c d) (hf : FeasiblePair p c d R t) :
    Real.sqrt (3 / 5) * sineReal t ^ 2 /
      ((15 + sineReal t ^ 2) * (angularDenominator p r : ℝ)) ≤
    pairAngularCost ((p.m : ℝ) * c) ((p.l : ℝ) * d) (cosineReal t ^ 2) := by
  have hm : (0 : ℝ) ≤ p.m := Nat.cast_nonneg _
  have hl : (0 : ℝ) ≤ p.l := Nat.cast_nonneg _
  have hterm : 0 < 2 - (p.m : ℝ) * c - (p.l : ℝ) * d := by
    linarith [hf.first_class, hf.second_class]
  have hterm_le : 2 - (p.m : ℝ) * c - (p.l : ℝ) * d ≤
      2 - (p.m : ℝ) * (r.lowerC : ℝ) - (p.l : ℝ) * (r.lowerD : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hcd.1 hm,
      mul_le_mul_of_nonneg_left hcd.2.2.1 hl]
  have he : (8 : ℝ) / 3 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hcoef : (2 : ℝ) / (3 * Real.exp 1) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * Real.exp 1)).mpr
    linarith
  let D : ℝ := 2 / 9 + (2 / (3 * Real.exp 1)) * (2 - (p.m : ℝ) * c - (p.l : ℝ) * d)
  have hD : 0 < D := by dsimp [D]; positivity
  have hDK : D ≤ (angularDenominator p r : ℝ) := by
    have hh := mul_le_mul hcoef hterm_le hterm.le (by norm_num : (0 : ℝ) ≤ 1 / 4)
    simpa [D, angularDenominator] using add_le_add_left hh ((2 : ℝ) / 9)
  have h := angular_denominator_antitone hD hDK (sq_nonneg (sineReal t))
  have hc : 1 - cosineReal t ^ 2 = sineReal t ^ 2 := by nlinarith [halfAngle_circle t]
  have hc' : 16 - cosineReal t ^ 2 = 15 + sineReal t ^ 2 := by linarith
  unfold pairAngularCost
  rw [hc, hc']
  exact h

/-- Full source charge comparison for a certified leaf under the genuine geometric constraints. -/
theorem Leaf.sound {p : Parameters} {r : Rectangle} {a : Leaf}
    (ha : a.Accepts p r) {c d R t : ℝ} (hcd : r.Contains c d)
    (hf : FeasiblePair p c d R t) :
    chargeReal p.q p.m c + chargeReal p.q p.l d + (1 : ℝ) / 4000 <
      pairAngularCost ((p.m : ℝ) * c) ((p.l : ℝ) * d) (cosineReal t ^ 2) := by
  have hp : p.Valid := ha.1
  have hr : r.InWindow p.q := ha.2.1
  exact (charges_le_sum hp hr hcd hf.first_class hf.second_class).trans_lt
    ((Leaf.angular_sound ha hcd hf).trans_le (coarse_angular_le_cost hp hr hcd hf))

#print axioms Leaf.angular_sound
#print axioms Leaf.sound

end CubeSections.Certificates
