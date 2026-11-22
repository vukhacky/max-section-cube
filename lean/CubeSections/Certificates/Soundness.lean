import CubeSections.Certificates.SourceSemantics

noncomputable section
namespace CubeSections.Certificates

/-- Analytic soundness of an accepted tree, combining coverage with real leaf soundness. -/
theorem Tree.sound (p : Parameters) (r : Rectangle) (tree : Tree)
    (haccept : tree.Accepts p r) (c d R t : ℝ)
    (hcd : r.Contains c d) (hf : FeasiblePair p c d R t) :
    chargeReal p.q p.m c + chargeReal p.q p.l d + (1 : ℝ) / 4000 <
      pairAngularCost ((p.m : ℝ) * c) ((p.l : ℝ) * d) (cosineReal t ^ 2) := by
  obtain ⟨s, a, _, hm, ha⟩ := tree.accepts_covers p r haccept c d hcd
  exact Leaf.sound ha hm hf

/-- Soundness in the source variable `s=cos² θ`, with the exact source radius factor. -/
theorem Tree.source_comparison (p : Parameters) (hp : p.Valid) (tree : Tree)
    (haccept : tree.Accepts p (rootRectangle p.q)) (c d s : ℝ)
    (hc₀ : 1 / ((p.q : ℝ) + 1) ≤ c) (hc₁ : c ≤ 1 / (p.q : ℝ))
    (hd₀ : 1 / ((p.q : ℝ) + 1) ≤ d) (hd₁ : d ≤ 1 / (p.q : ℝ))
    (hs₀ : 0 < s) (hs₁ : s < 1)
    (hproj : s ≤ (1 - (p.m : ℝ) * c) * (1 - (p.l : ℝ) * d) /
      (((p.m : ℝ) * c) * ((p.l : ℝ) * d)))
    (hstrip : SourceStripLaw p c d s) :
    chargeReal p.q p.m c + chargeReal p.q p.l d + (1 : ℝ) / 4000 <
      pairAngularCost ((p.m : ℝ) * c) ((p.l : ℝ) * d) s := by
  have hroot : (rootRectangle p.q).Contains c d := by
    simpa [Rectangle.Contains, rootRectangle] using And.intro hc₀ (And.intro hc₁ (And.intro hd₀ hd₁))
  have hf := source_to_feasible hp hc₀ hc₁ hd₀ hd₁ hs₀ hs₁ hproj hstrip
  have h := tree.sound p (rootRectangle p.q) haccept c d (sourceRadius p)
    ((1 - Real.sqrt s) / Real.sqrt (1-s)) hroot hf
  have hcos := (halfAngle_of_squared_cosine hs₀ hs₁).2.2.2
  simpa only [hcos, Real.sq_sqrt hs₀.le] using h

/-- The same comparison with the source's continuous endpoint convention for H. -/
theorem Tree.source_comparison_extended (p : Parameters) (hp : p.Valid) (tree : Tree)
    (haccept : tree.Accepts p (rootRectangle p.q)) (c d s : ℝ)
    (hc₀ : 1 / ((p.q : ℝ) + 1) ≤ c) (hc₁ : c ≤ 1 / (p.q : ℝ))
    (hd₀ : 1 / ((p.q : ℝ) + 1) ≤ d) (hd₁ : d ≤ 1 / (p.q : ℝ))
    (hs₀ : 0 < s) (hs₁ : s < 1)
    (hproj : s ≤ (1 - (p.m : ℝ) * c) * (1 - (p.l : ℝ) * d) /
      (((p.m : ℝ) * c) * ((p.l : ℝ) * d)))
    (hstrip : SourceStripLaw p c d s) :
    sourceCharge p.q p.m c + sourceCharge p.q p.l d + (1 : ℝ) / 4000 <
      pairAngularCost ((p.m : ℝ) * c) ((p.l : ℝ) * d) s := by
  have hq := Parameters.two_le_q hp
  have hf := source_to_feasible hp hc₀ hc₁ hd₀ hd₁ hs₀ hs₁ hproj hstrip
  rw [sourceCharge_eq_of_class_lt p.q p.m (by omega) c hf.first_class,
      sourceCharge_eq_of_class_lt p.q p.l (by omega) d hf.second_class]
  exact tree.source_comparison p hp haccept c d s hc₀ hc₁ hd₀ hd₁ hs₀ hs₁ hproj hstrip

#print axioms Tree.sound
#print axioms Tree.source_comparison

end CubeSections.Certificates
