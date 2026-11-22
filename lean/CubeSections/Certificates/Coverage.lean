import CubeSections.Certificates.Checker

/-!
# Structural coverage of the closed rectangle certificate trees

This result proves coverage and valid numeric leaves only. The interpretation of
a valid leaf as a real angular comparison is a separate analytic theorem.
-/
namespace CubeSections.Certificates

/-- Membership uses closed intervals, so a midpoint is never omitted. -/
def Rectangle.Contains (r : Rectangle) (c d : ℝ) : Prop :=
  (r.lowerC : ℝ) ≤ c ∧ c ≤ (r.upperC : ℝ) ∧
  (r.lowerD : ℝ) ≤ d ∧ d ≤ (r.upperD : ℝ)

/-- A leaf is reached by following the stated coordinate splits from its parent box. -/
def Tree.HasLeaf (r : Rectangle) : Tree → Rectangle → Leaf → Prop
  | .leaf a, s, b => s = r ∧ b = a
  | .splitC z left right, s, b =>
      left.HasLeaf (r.leftC z) s b ∨ right.HasLeaf (r.rightC z) s b
  | .splitD z left right, s, b =>
      left.HasLeaf (r.leftD z) s b ∨ right.HasLeaf (r.rightD z) s b

/-- Every point of the parent rectangle lies in an accepted leaf of the full tree. -/
theorem Tree.accepts_covers (p : Parameters) (r : Rectangle) (t : Tree)
    (h : t.Accepts p r) (c d : ℝ) (hcd : r.Contains c d) :
    ∃ (s : Rectangle) (a : Leaf),
      t.HasLeaf r s a ∧ s.Contains c d ∧ a.Accepts p s := by
  induction t generalizing r with
  | leaf a => exact ⟨r, a, ⟨rfl, rfl⟩, hcd, h⟩
  | splitC z left right ihl ihr =>
      rcases h with ⟨_, hl, hr⟩
      rcases hcd with ⟨hcx, hcX, hdy, hdY⟩
      by_cases hc : c ≤ (z : ℝ)
      · obtain ⟨s, a, hp, hm, ha⟩ := ihl (r.leftC z) hl ⟨hcx, hc, hdy, hdY⟩
        exact ⟨s, a, Or.inl hp, hm, ha⟩
      · obtain ⟨s, a, hp, hm, ha⟩ := ihr (r.rightC z) hr
          ⟨(lt_of_not_ge hc).le, hcX, hdy, hdY⟩
        exact ⟨s, a, Or.inr hp, hm, ha⟩
  | splitD z left right ihl ihr =>
      rcases h with ⟨_, hl, hr⟩
      rcases hcd with ⟨hcx, hcX, hdy, hdY⟩
      by_cases hd : d ≤ (z : ℝ)
      · obtain ⟨s, a, hp, hm, ha⟩ := ihl (r.leftD z) hl ⟨hcx, hcX, hdy, hd⟩
        exact ⟨s, a, Or.inl hp, hm, ha⟩
      · obtain ⟨s, a, hp, hm, ha⟩ := ihr (r.rightD z) hr
          ⟨hcx, hcX, (lt_of_not_ge hd).le, hdY⟩
        exact ⟨s, a, Or.inr hp, hm, ha⟩

/-- Boolean acceptance is converted to the same exact coverage statement. -/
theorem Tree.check_covers (p : Parameters) (r : Rectangle) (t : Tree)
    (h : t.check p r = true) (c d : ℝ) (hcd : r.Contains c d) :
    ∃ (s : Rectangle) (a : Leaf),
      t.HasLeaf r s a ∧ s.Contains c d ∧ a.Accepts p s :=
  t.accepts_covers p r ((t.check_eq_true_iff p r).mp h) c d hcd

/-- The leaf membership relation carries accepted arithmetic to any occurring leaf. -/
theorem Tree.accepts_leaf (p : Parameters) (r : Rectangle) (t : Tree)
    (h : t.Accepts p r) (s : Rectangle) (a : Leaf) (ha : t.HasLeaf r s a) :
    a.Accepts p s := by
  induction t generalizing r with
  | leaf b =>
      rcases ha with ⟨rfl, rfl⟩
      exact h
  | splitC z left right ihl ihr =>
      rcases h with ⟨_, hl, hr⟩
      rcases ha with hleft | hright
      · exact ihl (r.leftC z) hl hleft
      · exact ihr (r.rightC z) hr hright
  | splitD z left right ihl ihr =>
      rcases h with ⟨_, hl, hr⟩
      rcases ha with hleft | hright
      · exact ihl (r.leftD z) hl hleft
      · exact ihr (r.rightD z) hr hright

#print axioms Tree.accepts_covers
#print axioms Tree.check_covers
#print axioms Tree.accepts_leaf

end CubeSections.Certificates
