import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.DenselyOrdered

/-! Monotonicity through finitely many switching points, proved by finite
induction and the mean-value theorem on the two sides of each switch. -/

noncomputable section
open Set

namespace CubeSections

theorem monotoneOn_of_hasDerivAt_nonneg_off_finset (S : Finset ℝ)
    {f f' : ℝ → ℝ} {D : Set ℝ} (hD : Convex ℝ D) (hc : ContinuousOn f D)
    (hd : ∀ x ∈ interior D, x ∉ S → HasDerivAt f (f' x) x)
    (hp : ∀ x ∈ interior D, x ∉ S → 0 ≤ f' x) : MonotoneOn f D := by
  classical
  induction S using Finset.induction_on generalizing D with
  | empty =>
      apply monotoneOn_of_deriv_nonneg hD hc
      · intro x hx
        exact (hd x hx (by simp)).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hd x hx (by simp)).deriv]
        exact hp x hx (by simp)
  | @insert a S ha ih =>
      have hleft : MonotoneOn f (D ∩ Iic a) := by
        apply ih (hD.inter (convex_Iic a)) (hc.mono inter_subset_left)
        · intro x hx hs
          have hx' : x ∈ interior D ∧ x < a := by
            simpa only [interior_inter, interior_Iic, mem_inter_iff, mem_Iio] using hx
          exact hd x hx'.1 (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_lt hx'.2, hs⟩)
        · intro x hx hs
          have hx' : x ∈ interior D ∧ x < a := by
            simpa only [interior_inter, interior_Iic, mem_inter_iff, mem_Iio] using hx
          exact hp x hx'.1 (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_lt hx'.2, hs⟩)
      have hright : MonotoneOn f (D ∩ Ici a) := by
        apply ih (hD.inter (convex_Ici a)) (hc.mono inter_subset_left)
        · intro x hx hs
          have hx' : x ∈ interior D ∧ a < x := by
            simpa only [interior_inter, interior_Ici, mem_inter_iff, mem_Ioi] using hx
          exact hd x hx'.1 (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_gt hx'.2, hs⟩)
        · intro x hx hs
          have hx' : x ∈ interior D ∧ a < x := by
            simpa only [interior_inter, interior_Ici, mem_inter_iff, mem_Ioi] using hx
          exact hp x hx'.1 (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_gt hx'.2, hs⟩)
      intro x hx y hy hxy
      by_cases hya : y ≤ a
      · exact hleft ⟨hx, hxy.trans hya⟩ ⟨hy, hya⟩ hxy
      by_cases hax : a ≤ x
      · exact hright ⟨hx, hax⟩ ⟨hy, hax.trans hxy⟩ hxy
      have hxa : x ≤ a := (lt_of_not_ge hax).le
      have hay : a ≤ y := (lt_of_not_ge hya).le
      have haD : a ∈ D := hD.ordConnected.out hx hy ⟨hxa, hay⟩
      exact (hleft ⟨hx, hxa⟩ ⟨haD, by simp⟩ hxa).trans
        (hright ⟨haD, by simp⟩ ⟨hy, hay⟩ hay)

theorem monotone_of_hasDerivAt_nonneg_off_finset (S : Finset ℝ)
    {f f' : ℝ → ℝ} (hc : Continuous f)
    (hd : ∀ x, x ∉ S → HasDerivAt f (f' x) x)
    (hp : ∀ x, x ∉ S → 0 ≤ f' x) : Monotone f := by
  have h := monotoneOn_of_hasDerivAt_nonneg_off_finset S convex_univ hc.continuousOn
    (fun x _ hx => hd x hx) (fun x _ hx => hp x hx)
  exact fun x y hxy => h (mem_univ x) (mem_univ y) hxy

end CubeSections
