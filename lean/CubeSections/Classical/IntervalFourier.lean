import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! Exact characteristic-function normalization for one uniform cube coordinate.
The closed interval endpoints are null; no Fourier inversion is used here.
-/
noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ENNReal

namespace CubeSections

def unitIntervalMeasure : Measure ℝ := volume.restrict (Icc (-(1/2 : ℝ)) (1/2 : ℝ))

instance unitIntervalMeasure_probability : IsProbabilityMeasure unitIntervalMeasure where
  measure_univ := by
    simp only [unitIntervalMeasure, Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num

theorem integral_unitInterval_exp_eq_sinc (r : ℝ) :
    (∫ x : ℝ in (-(1/2 : ℝ))..(1/2 : ℝ),
      Complex.exp (((2*r*x : ℝ) : ℂ)*Complex.I)) = (Real.sinc r : ℂ) := by
  by_cases hr : r=0
  · norm_num [hr]
  have hc : 2*r ≠ 0 := mul_ne_zero (by norm_num) hr
  have h := intervalIntegral.integral_comp_mul_left
    (fun x : ℝ => Complex.exp ((x : ℂ)*Complex.I))
    (a := -(1/2 : ℝ)) (b := (1/2 : ℝ)) hc
  have hlo : 2*r*(-(1/2 : ℝ)) = -r := by ring
  have hhi : 2*r*(1/2 : ℝ) = r := by ring
  rw [hlo, hhi, integral_exp_mul_I_eq_sinc] at h
  calc
    _ = (2*r)⁻¹ • ((2 : ℂ)*(r : ℂ)*(Real.sinc r : ℂ)) := h
    _ = _ := by
      rw [Complex.real_smul]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hr]

theorem charFun_unitIntervalMeasure (t : ℝ) :
    charFun unitIntervalMeasure t = (Real.sinc (t/2) : ℂ) := by
  rw [charFun_apply_real]
  change (∫ x : ℝ in Icc (-(1/2 : ℝ)) (1/2 : ℝ),
    Complex.exp ((t : ℂ)*(x : ℂ)*Complex.I)) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : -(1/2 : ℝ) ≤ 1/2)]
  have h := integral_unitInterval_exp_eq_sinc (t/2)
  have hscale : 2*(t/2)=t := by ring
  simpa only [hscale, Complex.ofReal_mul] using h

/-- The source uses exp(2πitx), hence sinc(πt), with continuous value 1 at 0. -/
theorem charFun_unitIntervalMeasure_two_pi (t : ℝ) :
    charFun unitIntervalMeasure (2*Real.pi*t) = (Real.sinc (Real.pi*t) : ℂ) := by
  rw [charFun_unitIntervalMeasure]
  congr 2
  ring

theorem charFun_unitIntervalMeasure_neg_two_pi (t : ℝ) :
    charFun unitIntervalMeasure (-2*Real.pi*t) = (Real.sinc (Real.pi*t) : ℂ) := by
  rw [charFun_unitIntervalMeasure]
  have h : -2*Real.pi*t/2 = -(Real.pi*t) := by ring
  rw [h, Real.sinc_neg]

#print axioms charFun_unitIntervalMeasure
#print axioms charFun_unitIntervalMeasure_two_pi
end CubeSections
