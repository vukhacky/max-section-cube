import CubeSections.Certificates.SourceSemantics

/-! Scalar extraction of the direct strip law from exact two-row replacement. -/
noncomputable section
namespace CubeSections.Certificates
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def ExactStripAt (L loss R g u β : ℝ) : Prop :=
  (1 - loss + L * (1 / (1 - β) ^ 2 - 1)) *
    (max 0 (1 - R * β ^ 2 / (g * u))) ^ 2 ≤ 1

theorem reciprocal_square_penalty {a β : ℝ} (ha : 0 ≤ a) (haβ : a ≤ β) (hβ : β < 1) :
    1 / (1 - a / 2) ^ 2 - 1 ≤ a / (1 - β) := by
  have ha₁ : a < 1 := haβ.trans_lt hβ
  have hd : 0 < 1 - a := by linarith
  have hdβ : 0 < 1 - β := by linarith
  have hd₂ : 0 < 1 - a / 2 := by linarith
  have hsq : 1 - a ≤ (1 - a / 2) ^ 2 := by nlinarith [sq_nonneg a]
  have hinv : 1 / (1 - a / 2) ^ 2 ≤ 1 / (1 - a) :=
    div_le_div_of_nonneg_left (by norm_num) hd hsq
  have hid : 1 / (1 - a) - 1 = a / (1 - a) := by field_simp <;> ring
  have hfrac : a / (1 - a) ≤ a / (1 - β) :=
    div_le_div_of_nonneg_left ha hdβ (by linarith)
  linarith

theorem exactStripAt_optimized {L loss R g u : ℝ}
    (hL₀ : 0 ≤ L) (hL₁ : L ≤ 1) (hg : 0 < g) (hu : 0 < u)
    (hu₁ : u ≤ 1) (hgR : g ≤ R)
    (hexact : ExactStripAt L loss R g u (L * g * u / (2 * R))) :
    L ^ 2 / (2 * R * (1 - L * g * u / (2 * R)) ^ 2) ≤ loss / (g * u) := by
  have hR : 0 < R := hg.trans_le hgR
  let β := L * g * u / (2 * R)
  have hβ₀ : 0 ≤ β := by dsimp [β]; positivity
  have hLu : L * u ≤ 1 := by
    calc
      L * u ≤ 1 * 1 := mul_le_mul hL₁ hu₁ hu.le (by norm_num)
      _ = 1 := by ring
  have hnum : L * g * u ≤ R := by
    calc
      L * g * u = g * (L * u) := by ring
      _ ≤ g * 1 := mul_le_mul_of_nonneg_left hLu hg.le
      _ ≤ R := by simpa using hgR
  have hβ₁ : β ≤ 1 / 2 := by
    dsimp [β]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * R)).mpr
    nlinarith
  have hβlt : β < 1 := by linarith
  have hLβ : L * β ≤ β := by nlinarith [mul_le_mul_of_nonneg_right hL₁ hβ₀]
  have hLβ₀ : 0 ≤ L * β := mul_nonneg hL₀ hβ₀
  have hden : 0 < 1 - L * β / 2 := by linarith
  have hrelation : R * β ^ 2 / (g * u) = L * β / 2 := by
    dsimp [β]
    field_simp
    <;> ring
  change ExactStripAt L loss R g u β at hexact
  unfold ExactStripAt at hexact
  rw [hrelation, max_eq_right hden.le] at hexact
  have hdiv : 1 - loss + L * (1 / (1 - β) ^ 2 - 1) ≤
      1 / (1 - L * β / 2) ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hden)).mpr hexact
  have hpenalty := reciprocal_square_penalty hLβ₀ hLβ hβlt
  have hidentity : L * (1 / (1 - β) ^ 2 - 1) - L * β / (1 - β) =
      L * β / (1 - β) ^ 2 := by
    have hd : 1 - β ≠ 0 := ne_of_gt (by linarith : 0 < 1 - β)
    field_simp
    <;> ring
  have hloss : L * β / (1 - β) ^ 2 ≤ loss := by linarith
  have hcancel : L ^ 2 / (2 * R * (1 - β) ^ 2) =
      (L * β / (1 - β) ^ 2) / (g * u) := by
    have hd : 1 - β ≠ 0 := ne_of_gt (by linarith : 0 < 1 - β)
    dsimp [β]
    field_simp
    <;> ring
  change L ^ 2 / (2 * R * (1 - β) ^ 2) ≤ loss / (g * u)
  rw [hcancel]
  exact div_le_div_of_nonneg_right hloss (mul_pos hg hu).le

theorem unequal_row_loss {c d g u : ℝ} (hg : 0 < g) (hgsq : g ^ 2 = c * d)
    (hrow : |c - d| ≤ g ^ 2 * u ^ 2) :
    (c + d) / 2 - g ≤ g ^ 3 * u ^ 4 / 8 := by
  have hsq : (c - d) ^ 2 ≤ g ^ 4 * u ^ 4 := by
    have h := (sq_le_sq₀ (abs_nonneg (c-d)) (mul_nonneg (sq_nonneg g) (sq_nonneg u))).mpr hrow
    rw [sq_abs] at h
    convert h using 1 <;> ring
  have hlower : 8 * g * ((c + d) / 2 - g) ≤ (c - d) ^ 2 := by
    nlinarith [sq_nonneg ((c + d) / 2 - g)]
  have hmul : (8 * g) * ((c + d) / 2 - g) ≤ (8 * g) * (g ^ 3 * u ^ 4 / 8) := by
    convert hlower.trans hsq using 1 <;> ring
  exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 8 * g)).mp hmul

theorem directStrip_of_exact {c d ρ u R : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hu : 0 < u) (hu₁ : u ≤ 1)
    (hL₀ : 0 ≤ (c + d) / 2 + Real.sqrt (c*d) * ρ - c*d*u^2)
    (hL₁ : (c + d) / 2 + Real.sqrt (c*d) * ρ - c*d*u^2 ≤ 1)
    (hgR : Real.sqrt (c*d) ≤ R)
    (hrow : |c - d| ≤ c*d*u^2)
    (hexact : ExactStripAt ((c+d)/2 + Real.sqrt (c*d)*ρ - c*d*u^2)
      ((c+d)/2 - Real.sqrt (c*d)*ρ) R (Real.sqrt (c*d)) u
      (((c+d)/2 + Real.sqrt (c*d)*ρ - c*d*u^2) * Real.sqrt (c*d) * u / (2*R))) :
    ((c+d)/2 + Real.sqrt (c*d)*ρ - c*d*u^2)^2 /
      (2*R*(1-((c+d)/2 + Real.sqrt (c*d)*ρ - c*d*u^2)*Real.sqrt (c*d)*u/(2*R))^2)
      ≤ (1-ρ)/u + c*d/8*u^3 := by
  let g := Real.sqrt (c*d)
  have hg : 0 < g := Real.sqrt_pos.mpr (mul_pos hc hd)
  have hgsq : g^2 = c*d := Real.sq_sqrt (mul_pos hc hd).le
  have hmain := exactStripAt_optimized hL₀ hL₁ hg hu hu₁ hgR hexact
  have hrow' : |c-d| ≤ g^2*u^2 := by simpa only [hgsq] using hrow
  have hgap := unequal_row_loss hg hgsq hrow'
  have hloss : (c+d)/2-g*ρ ≤ g*(1-ρ)+g^3*u^4/8 := by linarith
  have hbound := div_le_div_of_nonneg_right hloss (mul_pos hg hu).le
  have hidentity : (g*(1-ρ)+g^3*u^4/8)/(g*u) = (1-ρ)/u + c*d/8*u^3 := by
    rw [← hgsq]
    field_simp
    <;> ring
  rw [hidentity] at hbound
  exact hmain.trans hbound

theorem rowDiscrepancy_of_reciprocal {c d s : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hrep : |c⁻¹-d⁻¹| ≤ 1-s) : |c-d| ≤ c*d*(1-s) := by
  have hid : (c*d)*(c⁻¹-d⁻¹) = d-c := by field_simp <;> ring
  rw [abs_sub_comm c d, ← hid, abs_mul, abs_of_pos (mul_pos hc hd)]
  exact mul_le_mul_of_nonneg_left hrep (mul_pos hc hd).le

def SourceExactStripLaw (p : Parameters) (c d s : ℝ) : Prop :=
  ∀ β : ℝ, 0 ≤ β → β ≤ 1 / 2 →
    ExactStripAt (sourceDeterminant c d s)
      ((c+d)/2 - Real.sqrt (c*d)*Real.sqrt s) (sourceRadius p)
      (Real.sqrt (c*d)) (Real.sqrt (1-s)) β

theorem sourceDeterminant_mem {q : ℕ} (hq : 2 ≤ q) {c d s : ℝ}
    (hc₀ : 1 / ((q : ℝ) + 1) ≤ c) (hc₁ : c ≤ 1 / (q : ℝ))
    (hd₀ : 1 / ((q : ℝ) + 1) ≤ d) (hd₁ : d ≤ 1 / (q : ℝ))
    (hs₀ : 0 < s) (hs₁ : s < 1) :
    0 < sourceDeterminant c d s ∧ sourceDeterminant c d s ≤ 1 := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hlower : (0 : ℝ) < 1 / ((q : ℝ)+1) := by positivity
  have hc := hlower.trans_le hc₀
  have hd := hlower.trans_le hd₀
  have hb : (1 : ℝ)/(q : ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hqpos).mpr
    linarith
  have hchalf := hc₁.trans hb
  have hdhalf := hd₁.trans hb
  have hcdhalf : c*d ≤ c/2 := by nlinarith [mul_le_mul_of_nonneg_left hdhalf hc.le]
  have hprodpos : 0 ≤ Real.sqrt (c*d)*Real.sqrt s := by positivity
  have htermpos : 0 ≤ c*d*s := by positivity
  constructor
  · unfold sourceDeterminant
    nlinarith
  · let t := (1-Real.sqrt s)/Real.sqrt (1-s)
    obtain ⟨_, _, hsin, hcos⟩ := halfAngle_of_squared_cosine hs₀ hs₁
    have hdet : determinantReal c d t = sourceDeterminant c d s := by
      simp only [determinantReal, sourceDeterminant, t, hsin, hcos,
        Real.sq_sqrt (show 0 ≤ 1-s by linarith)]
    rw [← hdet]
    exact determinantReal_le_one hq hc.le hd.le hc₁ hd₁

theorem sourceRadius_lower_general {p : Parameters} (hq : 1 ≤ p.q)
    (hm : p.m ≤ p.q) (hl : p.l ≤ p.q) : 1 / (p.q : ℝ) ≤ sourceRadius p := by
  have hq₀ : (0 : ℝ) < p.q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hb : (0 : ℝ) < 1 / (p.q : ℝ) := by positivity
  have hmR : (p.m : ℝ) ≤ p.q := by exact_mod_cast hm
  have hlR : (p.l : ℝ) ≤ p.q := by exact_mod_cast hl
  have hbase : (1 : ℝ) ≤ 1 + 1 / (p.q : ℝ) := by linarith
  have hexponent : (0 : ℝ) ≤ (p.q : ℝ) - ((p.m : ℝ) + (p.l : ℝ)) / 2 := by linarith
  have hpow := Real.one_le_rpow hbase hexponent
  have h := mul_le_mul_of_nonneg_left hpow hb.le
  simpa only [sourceRadius, mul_one] using h

theorem sourceDirectStrip_of_exact {p : Parameters} (hq : 2 ≤ p.q)
    (hm : p.m ≤ p.q) (hl : p.l ≤ p.q) {c d s : ℝ}
    (hc₀ : 1 / ((p.q : ℝ) + 1) ≤ c) (hc₁ : c ≤ 1 / (p.q : ℝ))
    (hd₀ : 1 / ((p.q : ℝ) + 1) ≤ d) (hd₁ : d ≤ 1 / (p.q : ℝ))
    (hs₀ : 0 < s) (hs₁ : s < 1)
    (hrow : |c-d| ≤ c*d*(1-s)) (hexact : SourceExactStripLaw p c d s) :
    SourceStripLaw p c d s := by
  have hqR : (2 : ℝ) ≤ p.q := by exact_mod_cast hq
  have hb : (0 : ℝ) < 1 / (p.q : ℝ) := by positivity
  have hlower : (0 : ℝ) < 1 / ((p.q : ℝ)+1) := by positivity
  have hc := hlower.trans_le hc₀
  have hd := hlower.trans_le hd₀
  have hu : 0 < Real.sqrt (1-s) := Real.sqrt_pos.mpr (by linarith)
  have husq : Real.sqrt (1-s)^2 = 1-s := Real.sq_sqrt (by linarith)
  have hu₁ : Real.sqrt (1-s) ≤ 1 := by nlinarith [Real.sqrt_nonneg (1-s)]
  have hg : 0 < Real.sqrt (c*d) := Real.sqrt_pos.mpr (mul_pos hc hd)
  have hprod : c*d ≤ (1/(p.q : ℝ))^2 := by
    simpa only [pow_two] using mul_le_mul hc₁ hd₁ hd.le hb.le
  have hgR : Real.sqrt (c*d) ≤ sourceRadius p :=
    ((Real.sqrt_le_left hb.le).mpr hprod).trans
      (sourceRadius_lower_general (by omega : 1 ≤ p.q) hm hl)
  have hR : 0 < sourceRadius p := hg.trans_le hgR
  obtain ⟨hL₀, hL₁⟩ := sourceDeterminant_mem hq hc₀ hc₁ hd₀ hd₁ hs₀ hs₁
  let β := sourceDeterminant c d s * Real.sqrt (c*d) * Real.sqrt (1-s) / (2*sourceRadius p)
  have hβ₀ : 0 ≤ β := by dsimp [β]; positivity
  have hmul : sourceDeterminant c d s * Real.sqrt (1-s) ≤ 1 := by
    simpa using mul_le_mul hL₁ hu₁ hu.le (by norm_num : (0 : ℝ) ≤ 1)
  have hnum : sourceDeterminant c d s * Real.sqrt (c*d) * Real.sqrt (1-s) ≤ sourceRadius p := by
    have h := mul_le_mul_of_nonneg_left hmul hg.le
    nlinarith
  have hβ₁ : β ≤ 1/2 := by
    dsimp [β]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*sourceRadius p)).mpr
    nlinarith
  have hopt := hexact β hβ₀ hβ₁
  have h := directStrip_of_exact hc hd hu hu₁
    (by simpa only [husq, sourceDeterminant] using hL₀.le)
    (by simpa only [husq, sourceDeterminant] using hL₁) hgR
    (by simpa only [husq] using hrow)
    (by simpa only [β, husq, sourceDeterminant] using hopt)
  simpa only [SourceStripLaw, sourceDeterminant, husq] using h

#print axioms exactStripAt_optimized
#print axioms unequal_row_loss
#print axioms directStrip_of_exact
#print axioms sourceDirectStrip_of_exact
end CubeSections.Certificates
