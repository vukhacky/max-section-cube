import CubeSections.Certificates.LeafSoundness
import CubeSections.Certificates.Radius
import CubeSections.Certificates.SourceAngle

noncomputable section
namespace CubeSections.Certificates

/-- The source charge, including its explicitly stated removable endpoint. -/
def sourceCharge (q j : ℕ) (c : ℝ) : ℝ :=
  if j = q ∧ c = 1 / (q : ℝ) then
    (1 - (q : ℝ) * Real.log (1 + 1 / (q : ℝ))) / 2
  else chargeReal q j c

theorem sourceCharge_eq_of_class_lt (q j : ℕ) (hq : 1 ≤ q) (c : ℝ)
    (hclass : (j : ℝ) * c < 1) : sourceCharge q j c = chargeReal q j c := by
  unfold sourceCharge
  split_ifs with h
  · exfalso
    have hq₀ : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hq))
    have heq : (j : ℝ) * c = 1 := by
      rw [h.1, h.2]
      field_simp
    linarith
  · rfl

/-- The manuscript determinant factor, with squared sine `1-s` expanded. -/
def sourceDeterminant (c d s : ℝ) : ℝ :=
  (c + d) / 2 + Real.sqrt (c * d) * Real.sqrt s - c * d * (1 - s)

/-- The exact direct-strip assumption used by Proposition 5.2 in the manuscript. -/
def SourceStripLaw (p : Parameters) (c d s : ℝ) : Prop :=
  sourceDeterminant c d s ^ 2 /
    (2 * sourceRadius p * (1 - sourceDeterminant c d s * Real.sqrt (c*d) *
      Real.sqrt (1-s) / (2 * sourceRadius p)) ^ 2) ≤
    (1 - Real.sqrt s) / Real.sqrt (1-s) + c*d/8 * Real.sqrt (1-s) ^ 3

/-- Source real parameters give the precise feasible-pair hypotheses used by the checker proof. -/
theorem source_to_feasible {p : Parameters} (hp : p.Valid) {c d s : ℝ}
    (hc₀ : 1 / ((p.q : ℝ) + 1) ≤ c) (hc₁ : c ≤ 1 / (p.q : ℝ))
    (hd₀ : 1 / ((p.q : ℝ) + 1) ≤ d) (hd₁ : d ≤ 1 / (p.q : ℝ))
    (hs₀ : 0 < s) (hs₁ : s < 1)
    (hproj : s ≤ (1 - (p.m : ℝ) * c) * (1 - (p.l : ℝ) * d) /
      (((p.m : ℝ) * c) * ((p.l : ℝ) * d)))
    (hstrip : SourceStripLaw p c d s) :
    FeasiblePair p c d (sourceRadius p) ((1 - Real.sqrt s) / Real.sqrt (1-s)) := by
  have hq := Parameters.two_le_q hp
  have hq' : (2 : ℝ) ≤ p.q := by exact_mod_cast hq
  have hq₀ : (0 : ℝ) < p.q := by linarith
  have hlow : (0 : ℝ) < 1 / ((p.q : ℝ) + 1) := by positivity
  have hcpos := hlow.trans_le hc₀
  have hdpos := hlow.trans_le hd₀
  have hmq : (p.m : ℝ) ≤ p.q := by exact_mod_cast hp.2.2.1.trans hp.2.2.2
  have hlq : (p.l : ℝ) ≤ p.q := by exact_mod_cast hp.2.2.2
  have hmc : (p.m : ℝ) * c ≤ 1 := by
    have hqc := (le_div_iff₀ hq₀).mp hc₁
    have hmul := mul_le_mul_of_nonneg_right hmq hcpos.le
    nlinarith
  have hld : (p.l : ℝ) * d ≤ 1 := by
    have hqd := (le_div_iff₀ hq₀).mp hd₁
    have hmul := mul_le_mul_of_nonneg_right hlq hdpos.le
    nlinarith
  have hmc' : (p.m : ℝ) * c < 1 := by
    by_contra h
    have heq : (p.m : ℝ) * c = 1 := le_antisymm hmc (le_of_not_gt h)
    simp only [heq, sub_self, zero_mul, zero_div] at hproj
    linarith
  have hld' : (p.l : ℝ) * d < 1 := by
    by_contra h
    have heq : (p.l : ℝ) * d = 1 := le_antisymm hld (le_of_not_gt h)
    simp only [heq, sub_self, mul_zero, zero_div] at hproj
    linarith
  let t := (1 - Real.sqrt s) / Real.sqrt (1-s)
  obtain ⟨ht₀, ht₁, hsin, hcos⟩ := halfAngle_of_squared_cosine hs₀ hs₁
  have hdet : determinantReal c d t = sourceDeterminant c d s := by
    simp only [determinantReal, sourceDeterminant, t, hsin, hcos,
      Real.sq_sqrt (show 0 ≤ 1-s by linarith)]
  have hsource : DirectStripLaw (determinantReal c d t) (sourceRadius p)
      (scaleReal c d (sourceRadius p) t) t (c*d) := by
    unfold DirectStripLaw scaleReal
    rw [hdet]
    change sourceDeterminant c d s ^ 2 /
      (2 * sourceRadius p *
        (1 - sourceDeterminant c d s * Real.sqrt (c*d) / (2 * sourceRadius p) * sineReal t) ^ 2) ≤
      t + c*d/8 * sineReal t ^ 3
    change sineReal t = Real.sqrt (1-s) at hsin
    rw [hsin, div_mul_eq_mul_div]
    exact hstrip
  refine ⟨ht₀, ht₁, hmc', hld', ?_, (sourceRadius_bounds hp).1,
    (sourceRadius_bounds hp).2, hsource⟩
  simpa only [hcos, Real.sq_sqrt hs₀.le] using hproj

#print axioms source_to_feasible

end CubeSections.Certificates
