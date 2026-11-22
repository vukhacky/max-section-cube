import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Finite weighted Hölder for nonnegative real functions, including the L¹
conclusion. Zero weights are allowed and contribute the factor `x ^ 0 = 1`.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace CubeSections

theorem finiteHolder_nonnegative
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) (f : ι → α → ℝ) (p : ι → ℝ)
    (hmeas : ∀ i, Measurable (f i))
    (hpos : ∀ i x, 0 ≤ f i x)
    (hint : ∀ i, Integrable (f i) μ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    Integrable (fun x => ∏ i, (f i x) ^ (p i)) μ ∧
      (∫ x, ∏ i, (f i x) ^ (p i) ∂μ) ≤
        ∏ i, (∫ x, f i x ∂μ) ^ (p i) := by
  classical
  let g : α → ℝ := fun x => ∏ i, (f i x) ^ (p i)
  let B : ℝ := ∏ i, (∫ x, f i x ∂μ) ^ (p i)
  have hgpos (x : α) : 0 ≤ g x :=
    Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hpos i x) _)
  have hBpos : 0 ≤ B :=
    Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (integral_nonneg (hpos i)) _)
  have hgm : Measurable g := by
    exact Finset.measurable_prod _ (fun i _ =>
      (Real.continuous_rpow_const (hp i)).measurable.comp (hmeas i))
  have hpoint (x : α) :
      ENNReal.ofReal (g x) = ∏ i, ENNReal.ofReal (f i x) ^ (p i) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hpos i x) _)]
    exact Finset.prod_congr rfl (fun i _ =>
      (ENNReal.ofReal_rpow_of_nonneg (hpos i x) (hp i)).symm)
  have hbound :
      (∏ i, (∫⁻ x, ENNReal.ofReal (f i x) ∂μ) ^ (p i)) = ENNReal.ofReal B := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ =>
      Real.rpow_nonneg (integral_nonneg (hpos i)) _)]
    apply Finset.prod_congr rfl
    intro i _
    rw [← ofReal_integral_eq_lintegral_ofReal (hint i) (ae_of_all _ (hpos i))]
    exact ENNReal.ofReal_rpow_of_nonneg (integral_nonneg (hpos i)) (hp i)
  have hholder := ENNReal.lintegral_prod_norm_pow_le (μ := μ) Finset.univ
    (f := fun i x => ENNReal.ofReal (f i x))
    (fun i _ => (hmeas i).ennreal_ofReal.aemeasurable)
    (by simpa using hsum) (fun i _ => hp i)
  simp only [hbound] at hholder
  have hle : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≤ ENNReal.ofReal B := by
    simpa only [hpoint] using hholder
  have hgi : Integrable g μ :=
    (lintegral_ofReal_ne_top_iff_integrable hgm.aestronglyMeasurable
      (ae_of_all _ hgpos)).1
      (ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top))
  refine ⟨hgi, ?_⟩
  change (∫ x, g x ∂μ) ≤ B
  rw [← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hgpos)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff hBpos).1 hle

#print axioms finiteHolder_nonnegative
end CubeSections
