import CubeSections.Classical.IntervalFourier
import CubeSections.Geometry.OrthogonalFibers
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The exact triangular density of a sum of two independent uniform
[-1/2,1/2] variables, and its squared L2 norm. All identities use actual
Lebesgue measures; closed interval endpoints are included. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubeSections

def tentDensity (x : ℝ) : ℝ := max (1-|x|) 0

theorem tentDensity_nonneg (x : ℝ) : 0 ≤ tentDensity x := le_max_right _ _

theorem continuous_tentDensity : Continuous tentDensity := by
  unfold tentDensity
  fun_prop

theorem measurable_tentDensity : Measurable tentDensity := continuous_tentDensity.measurable

@[simp] theorem tentDensity_neg (x : ℝ) : tentDensity (-x) = tentDensity x := by
  simp [tentDensity]

theorem tentDensity_even : Function.Even tentDensity := tentDensity_neg

theorem tentDensity_eq_zero_of_not_mem {x : ℝ} (hx : x ∉ Icc (-1 : ℝ) 1) : tentDensity x=0 := by
  have h : 1 ≤ |x| := by
    by_contra h
    have hh := abs_le.mp (le_of_lt (lt_of_not_ge h))
    exact hx hh
  exact max_eq_right (by linarith)

theorem tentDensity_hasCompactSupport : HasCompactSupport tentDensity :=
  HasCompactSupport.intro isCompact_Icc (fun x hx => tentDensity_eq_zero_of_not_mem hx)

theorem integrable_tentDensity : Integrable tentDensity :=
  continuous_tentDensity.integrable_of_hasCompactSupport tentDensity_hasCompactSupport

theorem integrable_tentDensity_sq : Integrable (fun x : ℝ => tentDensity x^2) := by
  apply (continuous_tentDensity.pow 2).integrable_of_hasCompactSupport
  exact HasCompactSupport.intro isCompact_Icc (fun x hx => by
    change tentDensity x^2=0
    rw [tentDensity_eq_zero_of_not_mem hx, zero_pow (by decide : (2 : ℕ) ≠ 0)])

theorem tentDensity_of_mem_Icc_zero_one {x : ℝ} (hx : x ∈ Icc 0 1) : tentDensity x=1-x := by
  rw [tentDensity, abs_of_nonneg hx.1, max_eq_left (by linarith [hx.2])]

theorem tentDensity_of_mem_Icc_neg_one_zero {x : ℝ} (hx : x ∈ Icc (-1) 0) : tentDensity x=1+x := by
  rw [tentDensity, abs_of_nonpos hx.2, max_eq_left (by linarith [hx.1])]
  ring

theorem integral_tentDensity_sq : (∫ x : ℝ, tentDensity x^2) = (2/3 : ℝ) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Icc (-1 : ℝ) 1) (fun x hx => by rw [tentDensity_eq_zero_of_not_mem hx]; norm_num),
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hleft : (∫ x : ℝ in (-1)..0, tentDensity x^2) = (1/3 : ℝ) := by
    have heq : (∫ x : ℝ in (-1)..0, tentDensity x^2) = ∫ x : ℝ in (-1)..0, (1+x)^2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [tentDensity_of_mem_Icc_neg_one_zero (by simpa using hx)]
    rw [heq, intervalIntegral.integral_comp_add_left (fun x : ℝ => x^2) 1]
    norm_num [integral_pow]
  have hright : (∫ x : ℝ in (0)..1, tentDensity x^2) = (1/3 : ℝ) := by
    have heq : (∫ x : ℝ in (0)..1, tentDensity x^2) = ∫ x : ℝ in (0)..1, (1-x)^2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [tentDensity_of_mem_Icc_zero_one (by simpa using hx)]
    rw [heq, intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^2) 1]
    norm_num [integral_pow]
  have hc : Continuous (fun x : ℝ => tentDensity x^2) := continuous_tentDensity.pow 2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := fun x : ℝ => tentDensity x^2) (μ := volume)
    (hc.intervalIntegrable (-1) 0) (hc.intervalIntegrable 0 1)
  rw [hleft,hright] at hsplit
  linarith

theorem ofReal_tentDensity (x : ℝ) : ENNReal.ofReal (tentDensity x) = ENNReal.ofReal (1-|x|) := by
  by_cases hx : 0 ≤ 1-|x|
  · rw [tentDensity,max_eq_left hx]
  · rw [tentDensity,max_eq_right (le_of_not_ge hx), ENNReal.ofReal_zero,
      ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hx)]

theorem unitInterval_overlap_mass (z : ℝ) :
    volume {x : ℝ | x ∈ Icc (-(1/2 : ℝ)) (1/2) ∧
      z-x ∈ Icc (-(1/2 : ℝ)) (1/2)} = ENNReal.ofReal (tentDensity z) := by
  have hset : {x : ℝ | x ∈ Icc (-(1/2 : ℝ)) (1/2) ∧
      z-x ∈ Icc (-(1/2 : ℝ)) (1/2)} =
      Icc (max (-(1/2 : ℝ)) (z-1/2)) (min (1/2 : ℝ) (z+1/2)) := by
    ext x
    simp only [mem_ofPred_eq, mem_Icc, max_le_iff, le_min_iff]
    constructor <;> rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩ <;> constructor <;> constructor <;> linarith
  rw [hset,Real.volume_Icc,ofReal_tentDensity]
  congr 1
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg hz,max_eq_right (by linarith),min_eq_left (by linarith)]
    ring
  · rw [abs_of_nonpos (le_of_not_ge hz),max_eq_left (by linarith),min_eq_right (by linarith)]
    ring

/-- Exact density of the sum of two independent uniform unit-interval variables. -/
theorem map_add_unitIntervalMeasure :
    Measure.map (fun p : ℝ×ℝ => p.1+p.2) (unitIntervalMeasure.prod unitIntervalMeasure) =
      volume.withDensity (fun z => ENNReal.ofReal (tentDensity z)) := by
  let I : Set ℝ := Icc (-(1/2 : ℝ)) (1/2)
  let e := MeasurableEquiv.shearAddRight ℝ
  have he : MeasurePreserving e ((volume : Measure ℝ).prod volume) (volume.prod volume) :=
    measurePreserving_prod_add volume volume
  have hI : MeasurableSet (I ×ˢ I) := measurableSet_Icc.prod measurableSet_Icc
  have hcomp : Prod.snd ∘ e = (fun p : ℝ×ℝ => p.1+p.2) := rfl
  calc
    _ = Measure.map Prod.snd (Measure.map e ((volume.prod volume).restrict (I ×ˢ I))) := by
      rw [Measure.map_map measurable_snd e.measurable, hcomp]
      congr 1
      exact Measure.prod_restrict I I
    _ = Measure.map Prod.snd ((volume.prod volume).restrict (e.symm ⁻¹' (I ×ˢ I))) := by
      rw [map_restrict_of_measurePreserving_equiv e _ _ he]
    _ = volume.withDensity (fun z : ℝ => volume
        ((fun x : ℝ => (x,z)) ⁻¹' (e.symm ⁻¹' (I ×ˢ I)))) :=
      map_snd_restrict_eq_fiberDensity volume volume _ (hI.preimage e.symm.measurable)
    _ = _ := by
      congr 1
      funext z
      convert unitInterval_overlap_mass z using 1
      congr 1
      ext x
      change (x ∈ I ∧ -x+z ∈ I) ↔ _
      simp only [I, mem_ofPred_eq, sub_eq_add_neg, add_comm]

#print axioms integral_tentDensity_sq
#print axioms map_add_unitIntervalMeasure
end CubeSections
