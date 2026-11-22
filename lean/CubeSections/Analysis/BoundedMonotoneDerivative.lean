import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! A bounded differentiable increasing real function has an L1 derivative.
The two half-line FTC arguments use the actual finite endpoint limits. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace CubeSections

theorem integrable_nonneg_deriv_of_bounded (g g' : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt g (g' x) x) (hnonneg : ∀ x, 0 ≤ g' x)
    (hb : ∃ C : ℝ, ∀ x, |g x| ≤ C) : Integrable g' := by
  obtain ⟨C, hC⟩ := hb
  have hm : Monotone g := monotone_of_deriv_nonneg
    (fun x => (hd x).differentiableAt) (fun x => by rw [(hd x).deriv]; exact hnonneg x)
  have habove : BddAbove (range g) := ⟨C, by
    rintro _ ⟨x, rfl⟩
    exact (le_abs_self _).trans (hC x)⟩
  have hbelow : BddBelow (range g) := ⟨-C, by
    rintro _ ⟨x, rfl⟩
    exact (abs_le.mp (hC x)).1⟩
  have hright : IntegrableOn g' (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hd x)
      (fun x _ => hnonneg x) (tendsto_atTop_ciSup hm habove)
  have hreflect : IntegrableOn (fun x => g' (-x)) (Ioi (0 : ℝ)) := by
    apply integrableOn_Ioi_deriv_of_nonneg' (g := fun x => -g (-x))
    · intro x _
      convert! ((hd (-x)).comp x (hasDerivAt_neg' x)).neg using 1 <;>
        simp [Function.comp_def]
    · intro x _
      exact hnonneg (-x)
    · exact ((tendsto_atBot_ciInf hm hbelow).comp tendsto_neg_atTop_atBot).neg
  have hleft : IntegrableOn g' (Iio (0 : ℝ)) := by
    apply (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg _)
      (Homeomorph.neg ℝ).measurableEmbedding).mp
    simpa [Function.comp_def] using hreflect
  have hleft' : IntegrableOn g' (Iic (0 : ℝ)) :=
    (integrableOn_Iic_iff_integrableOn_Iio).2 hleft
  have hwhole := hleft'.union hright
  simpa using hwhole

#print axioms integrable_nonneg_deriv_of_bounded
end CubeSections
