import CubeSections.Certificates.Coverage
import CubeSections.Certificates.ChargeSoundness
import CubeSections.Certificates.HalfAngle
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
namespace CubeSections.Certificates

/-- The determinant gain appearing in the source two-row comparison. -/
def determinantReal (c d t : ℝ) : ℝ :=
  (c + d) / 2 + Real.sqrt (c * d) * cosineReal t - c * d * sineReal t ^ 2

def scaleReal (c d R t : ℝ) : ℝ :=
  determinantReal c d t * Real.sqrt (c * d) / (2 * R)

theorem gramLower_cast (r : Rectangle) :
    (gramLower r : ℝ) = min (r.lowerC : ℝ) (r.lowerD : ℝ) := by
  simp [gramLower]

theorem determinantLower_cast (r : Rectangle) (T : ℚ) :
    (determinantLower r T : ℝ) =
      ((r.lowerC : ℝ) + (r.lowerD : ℝ)) / 2 +
        min (r.lowerC : ℝ) (r.lowerD : ℝ) * cosineReal (T : ℝ) -
        (r.upperC : ℝ) * (r.upperD : ℝ) * sineReal (T : ℝ) ^ 2 := by
  simp [determinantLower, gramLower_cast, sine_cast, cosine_cast]

theorem eta_cast (p : Parameters) (r : Rectangle) (T : ℚ) :
    (eta p r T : ℝ) = (determinantLower r T : ℝ) * (gramLower r : ℝ) /
      (2 * (radiusUpper p : ℝ)) := by
  simp [eta]

theorem Rectangle.point_bounds {r : Rectangle} {q : ℕ} (hr : r.InWindow q)
    {c d : ℝ} (hcd : r.Contains c d) :
    1 / ((q : ℝ) + 1) ≤ c ∧ c ≤ 1 / (q : ℝ) ∧
    1 / ((q : ℝ) + 1) ≤ d ∧ d ≤ 1 / (q : ℝ) := by
  rcases hr with ⟨hx, _, hX, hy, _, hY⟩
  rcases hcd with ⟨hcx, hcX, hdy, hdY⟩
  have hx' : 1 / ((q : ℝ) + 1) ≤ (r.lowerC : ℝ) := by simpa using (Rat.cast_le (K := ℝ)).mpr hx
  have hX' : (r.upperC : ℝ) ≤ 1 / (q : ℝ) := by simpa using (Rat.cast_le (K := ℝ)).mpr hX
  have hy' : 1 / ((q : ℝ) + 1) ≤ (r.lowerD : ℝ) := by simpa using (Rat.cast_le (K := ℝ)).mpr hy
  have hY' : (r.upperD : ℝ) ≤ 1 / (q : ℝ) := by simpa using (Rat.cast_le (K := ℝ)).mpr hY
  exact ⟨hx'.trans hcx, hcX.trans hX', hy'.trans hdy, hdY.trans hY'⟩

theorem Rectangle.lower_pos {r : Rectangle} {q : ℕ}
    (hq : 1 ≤ q) (hr : r.InWindow q) :
    (0 : ℝ) < r.lowerC ∧ (0 : ℝ) < r.lowerD := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have ha : (0 : ℝ) < 1 / ((q : ℝ) + 1) := by positivity
  have hx : 1 / ((q : ℝ) + 1) ≤ (r.lowerC : ℝ) := by simpa using (Rat.cast_le (K := ℝ)).mpr hr.1
  have hy : 1 / ((q : ℝ) + 1) ≤ (r.lowerD : ℝ) := by simpa using (Rat.cast_le (K := ℝ)).mpr hr.2.2.2.1
  exact ⟨ha.trans_le hx, ha.trans_le hy⟩

theorem Rectangle.product_upper {r : Rectangle} {q : ℕ}
    (hq : 1 ≤ q) (hr : r.InWindow q) {c d : ℝ} (hcd : r.Contains c d) :
    0 < c * d ∧ c * d ≤ (r.upperC : ℝ) * (r.upperD : ℝ) := by
  obtain ⟨hx, hy⟩ := Rectangle.lower_pos hq hr
  have hc := hx.trans_le hcd.1
  have hd := hy.trans_le hcd.2.2.1
  exact ⟨mul_pos hc hd, mul_le_mul hcd.2.1 hcd.2.2.2 hd.le (hc.le.trans hcd.2.1)⟩

theorem Rectangle.gramLower_le {r : Rectangle} {q : ℕ}
    (hq : 1 ≤ q) (hr : r.InWindow q) {c d : ℝ} (hcd : r.Contains c d) :
    0 < (gramLower r : ℝ) ∧ (gramLower r : ℝ) ≤ Real.sqrt (c * d) := by
  obtain ⟨hx, hy⟩ := Rectangle.lower_pos hq hr
  have hgm : 0 < min (r.lowerC : ℝ) (r.lowerD : ℝ) := lt_min hx hy
  have hgc : min (r.lowerC : ℝ) (r.lowerD : ℝ) ≤ c := (min_le_left _ _).trans hcd.1
  have hgd : min (r.lowerC : ℝ) (r.lowerD : ℝ) ≤ d := (min_le_right _ _).trans hcd.2.2.1
  have hh : (min (r.lowerC : ℝ) (r.lowerD : ℝ)) ^ 2 ≤ c * d := by
    simpa only [pow_two] using mul_le_mul hgc hgd hgm.le (hgm.le.trans hgc)
  rw [gramLower_cast]
  exact ⟨hgm, Real.le_sqrt_of_sq_le hh⟩

/-- The lower determinant bound is valid throughout the real rectangle and below T. -/
theorem Rectangle.determinantLower_le {r : Rectangle} {q : ℕ}
    (hq : 1 ≤ q) (hr : r.InWindow q) {c d t : ℝ} {T : ℚ}
    (hcd : r.Contains c d) (ht : 0 ≤ t) (htT : t ≤ (T : ℝ)) (hT : (T : ℝ) ≤ 1) :
    (determinantLower r T : ℝ) ≤ determinantReal c d t := by
  have hT₀ : (0 : ℝ) ≤ T := ht.trans htT
  have ht₁ : t ≤ 1 := htT.trans hT
  obtain ⟨hgm, hgg⟩ := Rectangle.gramLower_le hq hr hcd
  obtain ⟨hcd₀, hcdXY⟩ := Rectangle.product_upper hq hr hcd
  have hcos : cosineReal (T : ℝ) ≤ cosineReal t :=
    cosineReal_antitoneOn ⟨ht, ht₁⟩ ⟨hT₀, hT⟩ htT
  have hsin : sineReal t ≤ sineReal (T : ℝ) :=
    sineReal_monotoneOn ⟨ht, ht₁⟩ ⟨hT₀, hT⟩ htT
  have hcosp := cosineReal_nonneg hT₀ hT
  have hsint := sineReal_nonneg ht
  have hsinT := sineReal_nonneg hT₀
  have hfirst : (gramLower r : ℝ) * cosineReal (T : ℝ) ≤
      Real.sqrt (c * d) * cosineReal t :=
    mul_le_mul hgg hcos hcosp (Real.sqrt_nonneg _)
  have hsecond : c * d * sineReal t ^ 2 ≤
      (r.upperC : ℝ) * (r.upperD : ℝ) * sineReal (T : ℝ) ^ 2 :=
    mul_le_mul hcdXY ((sq_le_sq₀ hsint hsinT).mpr hsin) (sq_nonneg _)
      (hcd₀.le.trans hcdXY)
  rw [determinantLower_cast, ← gramLower_cast]
  unfold determinantReal
  nlinarith [hcd.1, hcd.2.2.1]

/-- For q≥2, the actual determinant factor is at most one. -/
theorem determinantReal_le_one {q : ℕ} (hq : 2 ≤ q) {c d t : ℝ}
    (hc₀ : 0 ≤ c) (hd₀ : 0 ≤ d)
    (hcb : c ≤ 1 / (q : ℝ)) (hdb : d ≤ 1 / (q : ℝ)) :
    determinantReal c d t ≤ 1 := by
  have hq₂ : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hb : (0 : ℝ) < 1 / (q : ℝ) := by positivity
  have hb₁ : (1 : ℝ) / (q : ℝ) ≤ 1 / 2 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < q) (by norm_num)).mpr
    linarith
  have hprod : c * d ≤ (1 / (q : ℝ)) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hcb hdb hd₀ hb.le
  have hgram : Real.sqrt (c * d) ≤ 1 / (q : ℝ) := (Real.sqrt_le_left hb.le).mpr hprod
  have hcos := mul_le_mul_of_nonneg_left (cosineReal_le_one t) (Real.sqrt_nonneg (c*d))
  have hlast : 0 ≤ c * d * sineReal t ^ 2 := by positivity
  unfold determinantReal
  nlinarith

/-- The rational scale is below the actual one whenever the determinant bound is positive. -/
theorem Rectangle.eta_le_scale {p : Parameters} {r : Rectangle} {T : ℚ}
    (hq : 1 ≤ p.q) (hr : r.InWindow p.q) {c d R t : ℝ}
    (hcd : r.Contains c d) (ht : 0 ≤ t) (htT : t ≤ (T : ℝ)) (hT : (T : ℝ) ≤ 1)
    (hA : 0 ≤ (determinantLower r T : ℝ)) (hR : 0 < R)
    (hRB : R ≤ (radiusUpper p : ℝ)) :
    (eta p r T : ℝ) ≤ scaleReal c d R t := by
  obtain ⟨hgm, hgg⟩ := Rectangle.gramLower_le hq hr hcd
  have hAL := Rectangle.determinantLower_le hq hr hcd ht htT hT
  have hL : 0 ≤ determinantReal c d t := hA.trans hAL
  have hnum : (determinantLower r T : ℝ) * (gramLower r : ℝ) ≤
      determinantReal c d t * Real.sqrt (c*d) :=
    mul_le_mul hAL hgg hgm.le hL
  have hB : (0 : ℝ) < radiusUpper p := hR.trans_le hRB
  rw [eta_cast]
  unfold scaleReal
  calc
    (determinantLower r T : ℝ) * (gramLower r : ℝ) / (2 * (radiusUpper p : ℝ)) ≤
        determinantReal c d t * Real.sqrt (c*d) / (2 * (radiusUpper p : ℝ)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ determinantReal c d t * Real.sqrt (c*d) / (2 * R) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith

/-- The actual scale lies in the source's safe interval [0,1/2]. -/
theorem scaleReal_mem {q : ℕ} (hq : 2 ≤ q) {c d R t : ℝ}
    (hc₀ : 0 ≤ c) (hd₀ : 0 ≤ d)
    (hcb : c ≤ 1 / (q : ℝ)) (hdb : d ≤ 1 / (q : ℝ))
    (hR : 1 / (q : ℝ) ≤ R) (hL : 0 ≤ determinantReal c d t) :
    0 ≤ scaleReal c d R t ∧ scaleReal c d R t ≤ 1 / 2 := by
  have hq₂ : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hb : (0 : ℝ) < 1 / (q : ℝ) := by positivity
  have hRp : 0 < R := hb.trans_le hR
  have hprod : c * d ≤ (1 / (q : ℝ)) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hcb hdb hd₀ hb.le
  have hgram : Real.sqrt (c * d) ≤ R :=
    ((Real.sqrt_le_left hb.le).mpr hprod).trans hR
  have hupper := determinantReal_le_one hq hc₀ hd₀ hcb hdb (t := t)
  unfold scaleReal
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * R)).mpr
    have hh := mul_le_mul_of_nonneg_right hupper (Real.sqrt_nonneg (c*d))
    nlinarith

#print axioms Rectangle.determinantLower_le
#print axioms Rectangle.eta_le_scale
#print axioms scaleReal_mem

end CubeSections.Certificates
