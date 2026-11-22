import CubeSections.Analysis.EntropyEnvelope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Sharp quadratic bound for the entropy excess, including strictness. -/

noncomputable section
open Set

namespace CubeSections

/-- A repeated-node interpolation sign theorem, proved by two mean-value applications. -/
theorem negative_inside_of_strictConvex_derivative
    (f g : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x)
    (hg : StrictConvexOn ℝ (Icc a b) g)
    (hfa : f a = 0) (hfb : f b = 0) (hga : g a = 0)
    {c : ℝ} (hc : c ∈ Ioo a b) : f c < 0 := by
  by_contra hneg
  have hfc : 0 ≤ f c := le_of_not_gt hneg
  obtain ⟨d, hd, hgd⟩ := exists_hasDerivAt_eq_slope f g hc.1
    (hf.mono (Icc_subset_Icc le_rfl hc.2.le))
    (fun x hx => hderiv x ⟨hx.1, hx.2.trans hc.2⟩)
  obtain ⟨e, he, hge⟩ := exists_hasDerivAt_eq_slope f g hc.2
    (hf.mono (Icc_subset_Icc hc.1.le le_rfl))
    (fun x hx => hderiv x ⟨hc.1.trans hx.1, hx.2⟩)
  have hgd₀ : 0 ≤ g d := by
    rw [hgd, hfa, sub_zero]
    exact div_nonneg hfc (sub_pos.mpr hc.1).le
  have hge₀ : g e ≤ 0 := by
    rw [hge, hfb, zero_sub]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hfc) (sub_pos.mpr hc.2).le
  have hlt := hg.lt_on_openSegment (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
    (show e ∈ Icc a b from ⟨(hc.1.trans he.1).le, he.2.le⟩)
    (ne_of_lt (hc.1.trans he.1))
    (Ioo_subset_openSegment (show d ∈ Ioo a e from ⟨hd.1, hd.2.trans he.1⟩))
  rw [hga, max_eq_left hge₀] at hlt
  exact (not_lt_of_ge hgd₀) hlt

/-- Sharp constant in the entropy quadratic chord estimate. -/
def sharpEntropyCoeff (q : ℕ) : ℝ :=
  ((q : ℝ) + 1) * Real.log (1 + 1 / (q : ℝ)) - 1

/-- Reciprocal-interval quadratic, positive strictly inside the interval. -/
def reciprocalQuadratic (q : ℕ) (c : ℝ) : ℝ :=
  (1 - (q : ℝ) * c) * (((q : ℝ) + 1) * c - 1)

def sharpEntropyGap (q : ℕ) (c : ℝ) : ℝ :=
  entropyExcess q c - sharpEntropyCoeff q * reciprocalQuadratic q c

def sharpEntropyGapDeriv (q : ℕ) (c : ℝ) : ℝ :=
  -Real.log ((q : ℝ) * c) +
    (-1 + (q : ℝ) * Real.log (1 + 1 / (q : ℝ)) - sharpEntropyCoeff q * (2 * (q : ℝ) + 1)) +
    (2 * sharpEntropyCoeff q * (q : ℝ) * ((q : ℝ) + 1)) * c

theorem hasDerivAt_entropyExcess (q : ℕ) (hq : 1 ≤ q) (c : ℝ) (hc : 0 < c) :
    HasDerivAt (entropyExcess q)
      (-Real.log ((q : ℝ) * c) - 1 + (q : ℝ) * Real.log (1 + 1 / (q : ℝ))) c := by
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hl := ((hasDerivAt_id c).const_mul (q : ℝ)).log (ne_of_gt (mul_pos hq₀ hc))
  have h := (((hasDerivAt_id c).neg.mul hl).sub
    ((((hasDerivAt_id c).const_mul (q : ℝ)).const_sub 1).mul_const
      (Real.log (1 + 1 / (q : ℝ)))))
  convert h using 1
  · rfl
  · dsimp
    field_simp
    ring

theorem hasDerivAt_reciprocalQuadratic (q : ℕ) (c : ℝ) :
    HasDerivAt (reciprocalQuadratic q)
      (2 * (q : ℝ) + 1 - 2 * (q : ℝ) * ((q : ℝ) + 1) * c) c := by
  have h := (((hasDerivAt_id c).const_mul (q : ℝ)).const_sub 1).mul
    (((hasDerivAt_id c).const_mul ((q : ℝ) + 1)).sub_const 1)
  convert h using 1
  · rfl
  · dsimp
    ring

theorem hasDerivAt_sharpEntropyGap (q : ℕ) (hq : 1 ≤ q) (c : ℝ) (hc : 0 < c) :
    HasDerivAt (sharpEntropyGap q) (sharpEntropyGapDeriv q c) c := by
  convert (hasDerivAt_entropyExcess q hq c hc).sub
    ((hasDerivAt_reciprocalQuadratic q c).const_mul (sharpEntropyCoeff q)) using 1
  · rfl
  · dsimp [sharpEntropyGapDeriv]
    ring

theorem sharpEntropyGapDeriv_strictConvex (q : ℕ) (hq : 1 ≤ q) :
    StrictConvexOn ℝ (Ioi 0) (sharpEntropyGapDeriv q) := by
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hlog : StrictConvexOn ℝ (Ioi 0) (fun c : ℝ => -Real.log ((q : ℝ) * c)) := by
    refine ⟨convex_Ioi 0, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have hne : (q : ℝ) * x ≠ (q : ℝ) * y := by
      intro heq
      exact hxy (mul_left_cancel₀ (ne_of_gt hq₀) heq)
    have h := strictConcaveOn_log_Ioi.2
      (show (q : ℝ) * x ∈ Ioi 0 from mul_pos hq₀ hx)
      (show (q : ℝ) * y ∈ Ioi 0 from mul_pos hq₀ hy) hne ha hb hab
    simp only [smul_eq_mul] at h ⊢
    have hid : (q : ℝ) * (a * x + b * y) = a * ((q : ℝ) * x) + b * ((q : ℝ) * y) := by ring
    rw [hid]
    linarith
  let K := -1 + (q : ℝ) * Real.log (1 + 1 / (q : ℝ)) - sharpEntropyCoeff q * (2 * (q : ℝ) + 1)
  let L := 2 * sharpEntropyCoeff q * (q : ℝ) * ((q : ℝ) + 1)
  have hlin : ConvexOn ℝ (Ioi 0) (fun c : ℝ => K + L * c) := by
    refine ⟨convex_Ioi 0, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    have hid : a * (K + L * x) + b * (K + L * y) = K + L * (a * x + b * y) := by
      calc
        _ = (a + b) * K + L * (a * x + b * y) := by ring
        _ = _ := by rw [hab]; ring
    exact hid.symm.le
  convert hlog.add_convexOn hlin using 1
  ext c
  dsimp [sharpEntropyGapDeriv, K, L]
  ring

private theorem reciprocal_left_log (q : ℕ) (hq : 1 ≤ q) :
    Real.log ((q : ℝ) * (1 / ((q : ℝ) + 1))) = -Real.log (1 + 1 / (q : ℝ)) := by
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hid : (q : ℝ) * (1 / ((q : ℝ) + 1)) = (1 + 1 / (q : ℝ))⁻¹ := by
    field_simp
  rw [hid, Real.log_inv]

theorem entropyExcess_left (q : ℕ) (hq : 1 ≤ q) :
    entropyExcess q (1 / ((q : ℝ) + 1)) = 0 := by
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  unfold entropyExcess
  rw [reciprocal_left_log q hq]
  field_simp
  ring

theorem entropyExcess_right (q : ℕ) (hq : 1 ≤ q) :
    entropyExcess q (1 / (q : ℝ)) = 0 := by
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  simp [entropyExcess, ne_of_gt hq₀]

theorem reciprocalQuadratic_left (q : ℕ) :
    reciprocalQuadratic q (1 / ((q : ℝ) + 1)) = 0 := by
  have hq₁ : (q : ℝ) + 1 ≠ 0 := by positivity
  simp [reciprocalQuadratic, hq₁]

theorem reciprocalQuadratic_right (q : ℕ) (hq : 1 ≤ q) :
    reciprocalQuadratic q (1 / (q : ℝ)) = 0 := by
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  simp [reciprocalQuadratic, ne_of_gt hq₀]

theorem sharpEntropyGapDeriv_left (q : ℕ) (hq : 1 ≤ q) :
    sharpEntropyGapDeriv q (1 / ((q : ℝ) + 1)) = 0 := by
  unfold sharpEntropyGapDeriv
  rw [reciprocal_left_log q hq]
  unfold sharpEntropyCoeff
  field_simp
  ring

theorem entropyExcess_lt_sharpQuadratic (q : ℕ) (hq : 1 ≤ q) (c : ℝ)
    (hc₀ : 1 / ((q : ℝ) + 1) < c) (hc₁ : c < 1 / (q : ℝ)) :
    entropyExcess q c < sharpEntropyCoeff q * reciprocalQuadratic q c := by
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have ha : (0 : ℝ) < 1 / ((q : ℝ) + 1) := by positivity
  have hcont : ContinuousOn (sharpEntropyGap q) (Icc (1 / ((q : ℝ) + 1)) (1 / (q : ℝ))) := by
    intro x hx
    exact (hasDerivAt_sharpEntropyGap q hq x (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  have hconv := (sharpEntropyGapDeriv_strictConvex q hq).subset
    (show Icc (1 / ((q : ℝ) + 1)) (1 / (q : ℝ)) ⊆ Ioi 0 from
      fun x hx => ha.trans_le hx.1) (convex_Icc _ _)
  have h := negative_inside_of_strictConvex_derivative
    (sharpEntropyGap q) (sharpEntropyGapDeriv q) (hc₀.trans hc₁) hcont
    (fun x hx => hasDerivAt_sharpEntropyGap q hq x (ha.trans hx.1)) hconv
    (by rw [sharpEntropyGap, entropyExcess_left q hq, reciprocalQuadratic_left]; ring)
    (by rw [sharpEntropyGap, entropyExcess_right q hq, reciprocalQuadratic_right q hq]; ring)
    (sharpEntropyGapDeriv_left q hq) ⟨hc₀, hc₁⟩
  exact sub_neg.mp h

theorem entropyExcess_le_sharpQuadratic (q : ℕ) (hq : 1 ≤ q) (c : ℝ)
    (hc₀ : 1 / ((q : ℝ) + 1) ≤ c) (hc₁ : c ≤ 1 / (q : ℝ)) :
    entropyExcess q c ≤ sharpEntropyCoeff q * reciprocalQuadratic q c := by
  rcases hc₀.eq_or_lt with h | h
  · subst c
    rw [entropyExcess_left q hq, reciprocalQuadratic_left]; simp
  rcases hc₁.eq_or_lt with h' | h'
  · subst c
    rw [entropyExcess_right q hq, reciprocalQuadratic_right q hq]; simp
  exact (entropyExcess_lt_sharpQuadratic q hq c h h').le

private def logSymmetricGap (x : ℝ) : ℝ := (x - x⁻¹) / 2 - Real.log x

private theorem hasDerivAt_logSymmetricGap (x : ℝ) (hx : 0 < x) :
    HasDerivAt logSymmetricGap ((x - 1)^2 / (2 * x^2)) x := by
  convert (((hasDerivAt_id x).sub (hasDerivAt_inv (ne_of_gt hx))).div_const 2).sub
    ((hasDerivAt_id x).log (ne_of_gt hx)) using 1
  · rfl
  · dsimp
    field_simp
    ring

theorem log_lt_half_sub_inv (x : ℝ) (hx : 1 < x) :
    Real.log x < (x - x⁻¹) / 2 := by
  have hmono : StrictMonoOn logSymmetricGap (Ici 1) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 1)
    · intro y hy
      exact (hasDerivAt_logSymmetricGap y (by have hy' : (1 : ℝ) ≤ y := hy; linarith)).continuousAt.continuousWithinAt
    · intro y hy
      exact (hasDerivAt_logSymmetricGap y (by have hy' : (1 : ℝ) ≤ y := interior_subset hy; linarith)).hasDerivWithinAt
    · intro y hy
      have hy₁ : 1 < y := by simpa using hy
      exact div_pos (sq_pos_of_pos (sub_pos.mpr hy₁)) (mul_pos (by norm_num) (sq_pos_of_pos (by linarith)))
  have h := hmono (show (1 : ℝ) ∈ Ici 1 by simp) (show x ∈ Ici 1 from hx.le) hx
  have hpos : 0 < (x - x⁻¹) / 2 - Real.log x := by simpa [logSymmetricGap] using h
  linarith

theorem sharpEntropyCoeff_pos (q : ℕ) (hq : 1 ≤ q) : 0 < sharpEntropyCoeff q := by
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hq₁ : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  let x : ℝ := 1 + 1 / (q : ℝ)
  have hx : 1 < x := by dsimp [x]; linarith [one_div_pos.mpr hq₀]
  have hx₀ : 0 < x := by linarith
  have hne : x⁻¹ ≠ 1 := by
    intro h
    have := congrArg (fun y : ℝ => y⁻¹) h
    simp only [inv_inv, inv_one] at this
    linarith
  have h := Real.log_lt_sub_one_of_pos (inv_pos.mpr hx₀) hne
  rw [Real.log_inv] at h
  have hid : ((q : ℝ) + 1) * (1 - x⁻¹) = 1 := by
    dsimp [x]
    field_simp
    ring
  have hmul := mul_lt_mul_of_pos_left (show 1 - x⁻¹ < Real.log x by linarith) hq₁
  rw [hid] at hmul
  change 0 < ((q : ℝ) + 1) * Real.log x - 1
  linarith

theorem sharpEntropyCoeff_lt (q : ℕ) (hq : 1 ≤ q) :
    sharpEntropyCoeff q < 1 / (2 * (q : ℝ)) := by
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hq₁ : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  let x : ℝ := 1 + 1 / (q : ℝ)
  have hx : 1 < x := by dsimp [x]; linarith [one_div_pos.mpr hq₀]
  have h := mul_lt_mul_of_pos_left (log_lt_half_sub_inv x hx) hq₁
  have hid : ((q : ℝ) + 1) * ((x - x⁻¹) / 2) - 1 = 1 / (2 * (q : ℝ)) := by
    dsimp [x]
    field_simp
    ring
  change ((q : ℝ) + 1) * Real.log x - 1 < _
  linarith

/-- Entropy excess is concave on the positive half-line. -/
theorem entropyExcess_concave (q : ℕ) (hq : 1 ≤ q) :
    ConcaveOn ℝ (Ioi 0) (entropyExcess q) := by
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  let g : ℝ → ℝ := fun c => -Real.log ((q : ℝ) * c) - 1 +
    (q : ℝ) * Real.log (1 + 1 / (q : ℝ))
  have hfirst (c : ℝ) (hc : 0 < c) : HasDerivAt (entropyExcess q) (g c) c :=
    hasDerivAt_entropyExcess q hq c hc
  have hsecond (c : ℝ) (hc : 0 < c) : HasDerivAt g (-(1 / c)) c := by
    have h := (((((hasDerivAt_id c).const_mul (q : ℝ)).log
      (ne_of_gt (mul_pos hq₀ hc))).neg).sub_const 1).add_const
      ((q : ℝ) * Real.log (1 + 1 / (q : ℝ)))
    convert h using 1
    · rfl
    · dsimp
      field_simp
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioi 0)
  · intro c hc
    exact (hfirst c hc).continuousAt.continuousWithinAt
  · intro c hc
    exact (hfirst c (interior_subset hc)).hasDerivWithinAt
  · intro c hc
    exact (hsecond c (interior_subset hc)).hasDerivWithinAt
  · intro c hc
    exact neg_nonpos.mpr (one_div_nonneg.mpr (le_of_lt (interior_subset hc)))

theorem entropyExcess_nonneg (q : ℕ) (hq : 1 ≤ q) (c : ℝ)
    (hc₀ : 1 / ((q : ℝ) + 1) ≤ c) (hc₁ : c ≤ 1 / (q : ℝ)) :
    0 ≤ entropyExcess q c := by
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have ha : (1 / ((q : ℝ) + 1)) ∈ Ioi 0 := Set.mem_Ioi.mpr (by positivity)
  have hb : (1 / (q : ℝ)) ∈ Ioi 0 := Set.mem_Ioi.mpr (one_div_pos.mpr hq₀)
  have h := (entropyExcess_concave q hq).ge_on_segment ha hb
    (Icc_subset_segment (show c ∈ Icc (1 / ((q : ℝ) + 1)) (1 / (q : ℝ)) from ⟨hc₀, hc₁⟩))
  rw [entropyExcess_left q hq, entropyExcess_right q hq, min_self] at h
  exact h

end CubeSections
