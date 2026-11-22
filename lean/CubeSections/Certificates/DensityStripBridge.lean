import CubeSections.Geometry.StripDensity
import CubeSections.Certificates.GeometricStripBridge
import CubeSections.Certificates.AllPairs

/-! From an explicit planar density cap to the exact source pair comparison.
The coarea/fiber bound remains the visible `SourcePairDensity` input. Maximality
supplies both the row discrepancy and the actual normalized competitor.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubeSections.Certificates

/-- The coarea/fiber input: a pushforward measure identity and an almost-everywhere
density bound. -/
def SourcePairDensity {n k : ℕ} (U : CubeSections.Frame n k) (p : Parameters)
    (i j : Fin n) (c d s : ℝ) : Prop :=
  ∃ ρ : ℝ × ℝ → ℝ≥0∞,
    Measure.map (CubeSections.normalizedPairCoordinates U i j)
      (volume.restrict (U ⁻¹' CubeSections.cube n)) = volume.withDensity ρ ∧
    ∀ᵐ z ∂volume, ρ z ≤ ENNReal.ofReal
      ((sourceRadius p / (4*Real.sqrt (c*d)*Real.sqrt (1-s))) * CubeSections.sectionVolume U)

theorem source_retained_volume_of_density {n k : ℕ} (U : CubeSections.Frame n k)
    (p : Parameters) (i j : Fin n) (c d s : ℝ)
    (hc : 0 < c) (hd : 0 < d) (hs : s < 1)
    (hdensity : SourcePairDensity U p i j c d s)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1/2) :
    max 0 (1-sourceRadius p*β^2/(Real.sqrt (c*d)*Real.sqrt (1-s))) *
      CubeSections.sectionVolume U ≤
      (volume ((U ⁻¹' CubeSections.cube n) ∩ CubeSections.twoRowStrip U i j β)).toReal := by
  obtain ⟨ρ,hmap,hcap⟩ := hdensity
  have hg : 0 < Real.sqrt (c*d) := Real.sqrt_pos.mpr (mul_pos hc hd)
  have hu : 0 < Real.sqrt (1-s) := Real.sqrt_pos.mpr (by linarith)
  have hR : 0 ≤ sourceRadius p := by unfold sourceRadius; positivity
  have hK : 0 ≤ sourceRadius p/(4*Real.sqrt (c*d)*Real.sqrt (1-s)) := by positivity
  have h := CubeSections.retained_volume_of_pair_density U i j ρ hmap
    (sourceRadius p/(4*Real.sqrt (c*d)*Real.sqrt (1-s))) hK hcap hβ₀ hβ₁
  have hscale : 4*(sourceRadius p/(4*Real.sqrt (c*d)*Real.sqrt (1-s)))*β^2 =
      sourceRadius p*β^2/(Real.sqrt (c*d)*Real.sqrt (1-s)) := by
    field_simp
    <;> ring
  simpa only [hscale, CubeSections.twoRowStrip] using h

/-- Direct strip law for an actual maximizing frame. The reciprocal row
discrepancy is derived from maximality; only the density cap remains analytic. -/
theorem sourceDirectStrip_of_maximizing_density {n k : ℕ} (U : CubeSections.Frame n k)
    (hU : CubeSections.IsMaximizingFrame U) (p : Parameters) (hq : 2 ≤ p.q)
    (hm : p.m ≤ p.q) (hl : p.l ≤ p.q)
    (i j : Fin n) (hij : i ≠ j) (c d s : ℝ)
    (hci : CubeSections.leverage U i = c) (hdj : CubeSections.leverage U j = d)
    (hc₀ : 1/((p.q : ℝ)+1) ≤ c) (hc₁ : c ≤ 1/(p.q : ℝ))
    (hd₀ : 1/((p.q : ℝ)+1) ≤ d) (hd₁ : d ≤ 1/(p.q : ℝ))
    (hs₀ : 0 < s) (hs₁ : s < 1) (hP : 0 ≤ CubeSections.gramProjection U i j)
    (hcorrelation : CubeSections.gramProjection U i j ^ 2 = c*d*s)
    (hdensity : SourcePairDensity U p i j c d s) : SourceStripLaw p c d s := by
  have hqR : (2 : ℝ) ≤ p.q := by exact_mod_cast hq
  have hb : (1 : ℝ)/(p.q : ℝ) < 1 :=
    (div_lt_one (by linarith : (0 : ℝ) < p.q)).mpr (by linarith)
  have hi : CubeSections.leverage U i < 1 := by rw [hci]; exact hc₁.trans_lt hb
  have hj : CubeSections.leverage U j < 1 := by rw [hdj]; exact hd₁.trans_lt hb
  have hrow := CubeSections.maximizing_leverage_gap U hU i j hi hj
  rw [hci,hdj,hcorrelation] at hrow
  have hrow' : |c-d| ≤ c*d*(1-s) := by nlinarith
  have hlow : (0 : ℝ) < 1/((p.q : ℝ)+1) := by positivity
  exact sourceDirectStrip_of_exact hq hm hl hc₀ hc₁ hd₀ hd₁ hs₀ hs₁ hrow'
    (sourceExactStrip_of_retained_volume U hU p hq i j hij c d s hci hdj hc₁ hd₁
      hs₀.le hP hcorrelation
      (source_retained_volume_of_density U p i j c d s (hlow.trans_le hc₀)
        (hlow.trans_le hd₀) hs₁ hdensity))

/-- Source Proposition 5.2 for a maximizing-frame pair, conditional on the
displayed density and grouped complementary-projection bounds. -/
theorem maximizing_smallQuotient_pair_comparison_of_density
    {n k : ℕ} (U : CubeSections.Frame n k) (hU : CubeSections.IsMaximizingFrame U)
    (q m l : ℕ) (hq : q=2 ∨ q=3 ∨ q=4)
    (hm₀ : 1 ≤ m) (hmq : m ≤ q) (hl₀ : 1 ≤ l) (hlq : l ≤ q)
    (i j : Fin n) (hij : i ≠ j) (c d s : ℝ)
    (hci : CubeSections.leverage U i = c) (hdj : CubeSections.leverage U j = d)
    (hc₀ : 1/((q : ℝ)+1) ≤ c) (hc₁ : c ≤ 1/(q : ℝ))
    (hd₀ : 1/((q : ℝ)+1) ≤ d) (hd₁ : d ≤ 1/(q : ℝ))
    (hs₀ : 0 < s) (hs₁ : s < 1) (hP : 0 ≤ CubeSections.gramProjection U i j)
    (hcorrelation : CubeSections.gramProjection U i j ^ 2 = c*d*s)
    (hprojection : s ≤ (1-(m : ℝ)*c)*(1-(l : ℝ)*d) /
      (((m : ℝ)*c)*((l : ℝ)*d)))
    (hdensity : SourcePairDensity U ⟨q,m,l⟩ i j c d s) :
    sourceCharge q m c + sourceCharge q l d + (1 : ℝ)/4000 <
      pairAngularCost ((m : ℝ)*c) ((l : ℝ)*d) s := by
  have hq₂ : 2 ≤ q := by rcases hq with rfl | rfl | rfl <;> omega
  exact smallQuotientPairComparison q m l hq hm₀ hmq hl₀ hlq c d s
    hc₀ hc₁ hd₀ hd₁ hs₀ hs₁ hprojection
    (sourceDirectStrip_of_maximizing_density U hU ⟨q,m,l⟩ hq₂ hmq hlq
      i j hij c d s hci hdj hc₀ hc₁ hd₀ hd₁ hs₀ hs₁ hP hcorrelation hdensity)

#print axioms source_retained_volume_of_density
#print axioms sourceDirectStrip_of_maximizing_density
#print axioms maximizing_smallQuotient_pair_comparison_of_density
end CubeSections.Certificates
