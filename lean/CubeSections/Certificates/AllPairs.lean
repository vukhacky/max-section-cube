import CubeSections.Certificates.AllPairsData
import CubeSections.Certificates.Soundness

noncomputable section
namespace CubeSections.Certificates

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Proposition 5.2 for ordered multiplicities. Every numeric certificate is discharged. -/
theorem sourcePair_comparison (p : Parameters) (hp : p.Valid) (c d s : ℝ)
    (hc₀ : 1 / ((p.q : ℝ) + 1) ≤ c) (hc₁ : c ≤ 1 / (p.q : ℝ))
    (hd₀ : 1 / ((p.q : ℝ) + 1) ≤ d) (hd₁ : d ≤ 1 / (p.q : ℝ))
    (hs₀ : 0 < s) (hs₁ : s < 1)
    (hproj : s ≤ (1 - (p.m : ℝ) * c) * (1 - (p.l : ℝ) * d) /
      (((p.m : ℝ) * c) * ((p.l : ℝ) * d)))
    (hstrip : SourceStripLaw p c d s) :
    sourceCharge p.q p.m c + sourceCharge p.q p.l d + (1 : ℝ) / 4000 <
      pairAngularCost ((p.m : ℝ) * c) ((p.l : ℝ) * d) s :=
  (certificate p).source_comparison_extended p hp (allPairs_accepts p hp)
    c d s hc₀ hc₁ hd₀ hd₁ hs₀ hs₁ hproj hstrip

/-- Proposition 5.2 for every multiplicity pair, using the exact source functions.
The hypotheses are the manuscript's reciprocal window, acute squared cosine,
complementary-projection inequality, and direct two-row strip law. -/
theorem smallQuotientPairComparison (q m l : ℕ)
    (hq : q = 2 ∨ q = 3 ∨ q = 4) (hm₀ : 1 ≤ m) (hmq : m ≤ q)
    (hl₀ : 1 ≤ l) (hlq : l ≤ q) (c d s : ℝ)
    (hc₀ : 1 / ((q : ℝ) + 1) ≤ c) (hc₁ : c ≤ 1 / (q : ℝ))
    (hd₀ : 1 / ((q : ℝ) + 1) ≤ d) (hd₁ : d ≤ 1 / (q : ℝ))
    (hs₀ : 0 < s) (hs₁ : s < 1)
    (hproj : s ≤ (1 - (m : ℝ) * c) * (1 - (l : ℝ) * d) /
      (((m : ℝ) * c) * ((l : ℝ) * d)))
    (hstrip : SourceStripLaw ⟨q,m,l⟩ c d s) :
    sourceCharge q m c + sourceCharge q l d + (1 : ℝ) / 4000 <
      pairAngularCost ((m : ℝ) * c) ((l : ℝ) * d) s := by
  by_cases hml : m ≤ l
  · exact sourcePair_comparison ⟨q,m,l⟩ ⟨hq,hm₀,hml,hlq⟩ c d s
      hc₀ hc₁ hd₀ hd₁ hs₀ hs₁ hproj hstrip
  · have hlm : l ≤ m := (lt_of_not_ge hml).le
    have hproj' : s ≤ (1 - (l : ℝ) * d) * (1 - (m : ℝ) * c) /
        (((l : ℝ) * d) * ((m : ℝ) * c)) := by
      simpa only [mul_comm] using hproj
    have hstrip' : SourceStripLaw ⟨q,l,m⟩ d c s := by
      simpa only [SourceStripLaw, sourceDeterminant, sourceRadius,
        add_comm, mul_comm, mul_left_comm, mul_assoc] using hstrip
    have h := sourcePair_comparison ⟨q,l,m⟩ ⟨hq,hl₀,hlm,hmq⟩ d c s
      hd₀ hd₁ hc₀ hc₁ hs₀ hs₁ hproj' hstrip'
    have hcost : pairAngularCost ((l : ℝ) * d) ((m : ℝ) * c) s =
        pairAngularCost ((m : ℝ) * c) ((l : ℝ) * d) s := by
      unfold pairAngularCost
      congr 2
      ring
    rw [hcost] at h
    simpa only [add_comm, add_left_comm, add_assoc] using h

#print axioms sourcePair_comparison
#print axioms smallQuotientPairComparison

end CubeSections.Certificates
