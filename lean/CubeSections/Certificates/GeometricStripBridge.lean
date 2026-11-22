import CubeSections.Geometry.StripCompetitor
import CubeSections.Certificates.DirectStripExtraction

/-! Source strip laws from the actual maximizing-frame competitor.
The retained-volume estimate is deliberately explicit. No density/coarea theorem
is asserted by this bridge; it supplies the determinant and scalar implications.
-/
noncomputable section
open Set MeasureTheory
namespace CubeSections.Certificates

theorem nonnegative_eq_sqrt_product {P c d s : ℝ}
    (hP : 0 ≤ P) (hc : 0 ≤ c) (hd : 0 ≤ d) (hs : 0 ≤ s)
    (hcorrelation : P^2 = c*d*s) : P = Real.sqrt (c*d)*Real.sqrt s := by
  apply (sq_eq_sq₀ hP (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hc hd), Real.sq_sqrt hs]
  exact hcorrelation

/-- Exact source replacement law, with the actual retained section volume visible. -/
theorem sourceExactStrip_of_retained_volume {n k : ℕ} (U : CubeSections.Frame n k)
    (hU : CubeSections.IsMaximizingFrame U) (p : Parameters) (hq : 2 ≤ p.q)
    (i j : Fin n) (hij : i ≠ j) (c d s : ℝ)
    (hci : CubeSections.leverage U i = c) (hdj : CubeSections.leverage U j = d)
    (hc₁ : c ≤ 1/(p.q : ℝ)) (hd₁ : d ≤ 1/(p.q : ℝ))
    (hs : 0 ≤ s) (hP : 0 ≤ CubeSections.gramProjection U i j)
    (hcorrelation : CubeSections.gramProjection U i j ^ 2 = c*d*s)
    (hretained : ∀ β : ℝ, 0 ≤ β → β ≤ 1/2 →
      max 0 (1-sourceRadius p*β^2/(Real.sqrt (c*d)*Real.sqrt (1-s))) *
        CubeSections.sectionVolume U ≤
        (volume ((U ⁻¹' CubeSections.cube n) ∩ CubeSections.twoRowStrip U i j β)).toReal) :
    SourceExactStripLaw p c d s := by
  have hqR : (2 : ℝ) ≤ p.q := by exact_mod_cast hq
  have hq₀ : (0 : ℝ) < p.q := by linarith
  have hb : (1 : ℝ)/(p.q : ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hq₀).mpr
    linarith
  have hi : CubeSections.leverage U i ≤ 1/2 := by rw [hci]; exact hc₁.trans hb
  have hj : CubeSections.leverage U j ≤ 1/2 := by rw [hdj]; exact hd₁.trans hb
  have hc : 0 ≤ c := by rw [← hci]; exact CubeSections.leverage_nonneg U i
  have hd : 0 ≤ d := by rw [← hdj]; exact CubeSections.leverage_nonneg U j
  have hPeq := nonnegative_eq_sqrt_product hP hc hd hs hcorrelation
  intro β hβ₀ hβ₁
  have h := CubeSections.maximizing_mergeRows_det_mul_retained_sq_le U hU i j hij
    β hβ₀ hβ₁ hi hj hP
    (max 0 (1-sourceRadius p*β^2/(Real.sqrt (c*d)*Real.sqrt (1-s))))
    (le_max_left _ _) (hretained β hβ₀ hβ₁)
  rw [hci, hdj, hcorrelation, hPeq] at h
  unfold ExactStripAt sourceDeterminant
  convert h using 1 <;> ring

/-- Direct source strip law from maximality, actual retained volume, and the
reciprocal row-replacement inequality. -/
theorem sourceDirectStrip_of_retained_volume {n k : ℕ} (U : CubeSections.Frame n k)
    (hU : CubeSections.IsMaximizingFrame U) (p : Parameters) (hq : 2 ≤ p.q)
    (hm : p.m ≤ p.q) (hl : p.l ≤ p.q)
    (i j : Fin n) (hij : i ≠ j) (c d s : ℝ)
    (hci : CubeSections.leverage U i = c) (hdj : CubeSections.leverage U j = d)
    (hc₀ : 1/((p.q : ℝ)+1) ≤ c) (hc₁ : c ≤ 1/(p.q : ℝ))
    (hd₀ : 1/((p.q : ℝ)+1) ≤ d) (hd₁ : d ≤ 1/(p.q : ℝ))
    (hs₀ : 0 < s) (hs₁ : s < 1) (hP : 0 ≤ CubeSections.gramProjection U i j)
    (hcorrelation : CubeSections.gramProjection U i j ^ 2 = c*d*s)
    (hrep : |c⁻¹-d⁻¹| ≤ 1-s)
    (hretained : ∀ β : ℝ, 0 ≤ β → β ≤ 1/2 →
      max 0 (1-sourceRadius p*β^2/(Real.sqrt (c*d)*Real.sqrt (1-s))) *
        CubeSections.sectionVolume U ≤
        (volume ((U ⁻¹' CubeSections.cube n) ∩ CubeSections.twoRowStrip U i j β)).toReal) :
    SourceStripLaw p c d s := by
  have hlower : (0 : ℝ) < 1/((p.q : ℝ)+1) := by positivity
  have hrow := rowDiscrepancy_of_reciprocal (hlower.trans_le hc₀) (hlower.trans_le hd₀) hrep
  exact sourceDirectStrip_of_exact hq hm hl hc₀ hc₁ hd₀ hd₁ hs₀ hs₁ hrow
    (sourceExactStrip_of_retained_volume U hU p hq i j hij c d s hci hdj hc₁ hd₁
      hs₀.le hP hcorrelation hretained)

#print axioms sourceExactStrip_of_retained_volume
#print axioms sourceDirectStrip_of_retained_volume
end CubeSections.Certificates
