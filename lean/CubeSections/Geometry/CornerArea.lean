import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Exact area removed by the normalized two-row strip. The square is closed;
the removed strip is open, and the four boundary segments are treated as null.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubeSections

def upperSquareCorner (t : ℝ) : Set (ℝ × ℝ) :=
  {p | -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1 ∧
    2 * (1-t) < p.1 + p.2}

def lowerSquareCorner (t : ℝ) : Set (ℝ × ℝ) :=
  Neg.neg ⁻¹' upperSquareCorner t

def squareRemovedCorners (t : ℝ) : Set (ℝ × ℝ) :=
  {p | -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1 ∧
    2 * (1-t) < |p.1 + p.2|}

theorem measurableSet_upperSquareCorner (t : ℝ) : MeasurableSet (upperSquareCorner t) := by
  unfold upperSquareCorner
  measurability

theorem measurableSet_lowerSquareCorner (t : ℝ) : MeasurableSet (lowerSquareCorner t) :=
  (measurableSet_upperSquareCorner t).preimage measurable_neg

theorem measurableSet_squareRemovedCorners (t : ℝ) :
    MeasurableSet (squareRemovedCorners t) := by
  unfold squareRemovedCorners
  measurability

theorem integral_corner_height {t : ℝ} (ht : 0 ≤ t) :
    (∫ x in Ioo (1-2*t) 1, (1-(2*(1-t)-x))) = 2*t^2 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show 1-2*t ≤ (1 : ℝ) by linarith)]
  have hf : (fun x : ℝ => 1-(2*(1-t)-x)) = (fun x : ℝ => x+(2*t-1)) := by
    funext x
    ring
  rw [hf]
  have hadd : (∫ x in (1-2*t)..1, x+(2*t-1)) =
      (∫ x in (1-2*t)..1, x) + (∫ _ in (1-2*t)..1, (2*t-1)) :=
    intervalIntegral.integral_add (continuous_id.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
  rw [hadd, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem volume_upperCorner_region {t : ℝ} (ht : 0 ≤ t) :
    volume (regionBetween (fun x : ℝ => 2*(1-t)-x) (fun _ => 1) (Ioo (1-2*t) 1)) =
      ENNReal.ofReal (2*t^2) := by
  have hf : IntegrableOn (fun x : ℝ => 2*(1-t)-x) (Ioo (1-2*t) 1) :=
    (continuous_const.sub continuous_id).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hg : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo (1-2*t) 1) :=
    continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have h := volume_regionBetween_eq_integral hf hg measurableSet_Ioo
    (fun x hx => by linarith [hx.1])
  change volume _ = _ at h
  simpa only [Pi.sub_apply, integral_corner_height ht] using h

theorem volume_upperSquareCorner {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1/2) :
    volume (upperSquareCorner t) = ENNReal.ofReal (2*t^2) := by
  let r := regionBetween (fun x : ℝ => 2*(1-t)-x) (fun _ => 1) (Ioo (1-2*t) 1)
  have hsub : r ⊆ upperSquareCorner t := by
    rintro p ⟨⟨hx₀,hx₁⟩,⟨hy₀,hy₁⟩⟩
    change -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1 ∧ 2*(1-t)<p.1+p.2
    refine ⟨?_,hx₁.le,?_,hy₁.le,?_⟩ <;> linarith
  have hbd : upperSquareCorner t \ r ⊆
      ({1} ×ˢ (univ : Set ℝ)) ∪ ((univ : Set ℝ) ×ˢ {1}) := by
    rintro p ⟨hp,hpr⟩
    rcases hp with ⟨hx₀,hx₁,hy₀,hy₁,hs⟩
    by_cases hx : p.1 = 1
    · exact Or.inl ⟨hx,mem_univ _⟩
    by_cases hy : p.2 = 1
    · exact Or.inr ⟨mem_univ _,hy⟩
    exfalso
    apply hpr
    change (1-2*t < p.1 ∧ p.1 < 1) ∧ (2*(1-t)-p.1 < p.2 ∧ p.2 < 1)
    exact ⟨⟨by linarith,lt_of_le_of_ne hx₁ hx⟩,⟨by linarith,lt_of_le_of_ne hy₁ hy⟩⟩
  have hb₁ : volume ({1} ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hb₂ : volume ((univ : Set ℝ) ×ˢ {1} : Set (ℝ × ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hnull : volume (upperSquareCorner t \ r) = 0 :=
    measure_mono_null hbd (measure_union_null hb₁ hb₂)
  rw [← measure_eq_measure_of_null_sdiff hsub hnull]
  exact volume_upperCorner_region ht₀

theorem volume_lowerSquareCorner {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1/2) :
    volume (lowerSquareCorner t) = ENNReal.ofReal (2*t^2) := by
  have hn : MeasurePreserving (Neg.neg : ℝ × ℝ → ℝ × ℝ) volume volume :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  rw [lowerSquareCorner, hn.measure_preimage
    (measurableSet_upperSquareCorner t).nullMeasurableSet]
  exact volume_upperSquareCorner ht₀ ht₁

theorem squareRemovedCorners_eq_union (t : ℝ) :
    squareRemovedCorners t = upperSquareCorner t ∪ lowerSquareCorner t := by
  ext p
  simp only [squareRemovedCorners, upperSquareCorner, lowerSquareCorner,
    mem_setOf_eq, mem_union, mem_preimage, Prod.fst_neg, Prod.snd_neg]
  constructor
  · rintro ⟨hx₀,hx₁,hy₀,hy₁,hs⟩
    rcases lt_abs.mp hs with hp | hn
    · exact Or.inl ⟨hx₀,hx₁,hy₀,hy₁,hp⟩
    · right
      refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith
  · rintro (⟨hx₀,hx₁,hy₀,hy₁,hs⟩ | ⟨hx₀,hx₁,hy₀,hy₁,hs⟩)
    · exact ⟨hx₀,hx₁,hy₀,hy₁,lt_abs.mpr (Or.inl hs)⟩
    · refine ⟨?_,?_,?_,?_,lt_abs.mpr (Or.inr ?_)⟩ <;> linarith

theorem squareCorners_disjoint {t : ℝ} (ht : t ≤ 1/2) :
    Disjoint (upperSquareCorner t) (lowerSquareCorner t) := by
  apply Set.disjoint_left.mpr
  intro p hu hl
  have hu' : 2*(1-t)<p.1+p.2 := hu.2.2.2.2
  have hl' : 2*(1-t)< -p.1-p.2 := by
    simpa only [lowerSquareCorner, mem_preimage, upperSquareCorner,
      mem_setOf_eq, Prod.fst_neg, Prod.snd_neg, sub_eq_add_neg] using hl.2.2.2.2
  linarith

/-- The exact two-corner area. Closed-square boundary points and t=0 are included. -/
theorem volume_squareRemovedCorners {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1/2) :
    volume (squareRemovedCorners t) = ENNReal.ofReal (4*t^2) := by
  rw [squareRemovedCorners_eq_union,
    measure_union (squareCorners_disjoint ht₁) (measurableSet_lowerSquareCorner t),
    volume_upperSquareCorner ht₀ ht₁, volume_lowerSquareCorner ht₀ ht₁,
    ← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 2*t^2)
      (by positivity : (0 : ℝ) ≤ 2*t^2)]
  congr 1
  ring

#print axioms volume_squareRemovedCorners
end CubeSections
