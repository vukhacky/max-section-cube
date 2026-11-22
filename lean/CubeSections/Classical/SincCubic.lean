import CubeSections.Classical.BallFour
import CubeSections.Classical.SincNegative

/-! The exact signed cubic sinc integral. Fourier pairing between the unit-box
density and the integrable squared sinc identifies it with the integral of the
tent density over [-1/2,1/2], equal to 3/4. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform RealInnerProductSpace ENNReal
namespace CubeSections

def unitBoxDensity : ℝ → ℝ := (Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => 1)

theorem measurable_unitBoxDensity : Measurable unitBoxDensity :=
  measurable_const.indicator measurableSet_Icc

theorem unitBoxDensity_nonneg (x : ℝ) : 0 ≤ unitBoxDensity x := by
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

theorem integrable_unitBoxDensity : Integrable unitBoxDensity := by
  change Integrable ((Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ : ℝ => (1 : ℝ))) volume
  exact (continuous_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ => (1 : ℝ))
    (Icc (-(1/2 : ℝ)) (1/2)) (volume : Measure ℝ)).integrable_indicator measurableSet_Icc

theorem unitBoxDensity_withDensity :
    volume.withDensity (fun x => ENNReal.ofReal (unitBoxDensity x)) = unitIntervalMeasure := by
  have heq : (fun x => ENNReal.ofReal (unitBoxDensity x)) =
      (Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)
    · simp only [unitBoxDensity, Set.indicator_of_mem hx, ENNReal.ofReal_one]
    · simp only [unitBoxDensity, Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
  rw [heq]
  change volume.withDensity ((Icc (-(1/2 : ℝ)) (1/2)).indicator (1 : ℝ → ℝ≥0∞)) =
    volume.restrict (Icc (-(1/2 : ℝ)) (1/2))
  exact withDensity_indicator_one measurableSet_Icc

theorem fourier_unitBoxDensity (t : ℝ) :
    𝓕 (fun x => (unitBoxDensity x : ℂ)) t = (Real.sinc (Real.pi*t) : ℂ) := by
  rw [fourier_nonnegative_real_density_eq_charFun unitBoxDensity
    measurable_unitBoxDensity unitBoxDensity_nonneg, unitBoxDensity_withDensity]
  exact charFun_unitIntervalMeasure_neg_two_pi t

theorem integral_unitBoxDensity_mul_tentDensity :
    (∫ x : ℝ, unitBoxDensity x * tentDensity x) = (3/4 : ℝ) := by
  have heq : (fun x => unitBoxDensity x * tentDensity x) =
      (Icc (-(1/2 : ℝ)) (1/2)).indicator tentDensity := by
    funext x
    by_cases hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)
    · simp only [unitBoxDensity, Set.indicator_of_mem hx, one_mul]
    · simp only [unitBoxDensity, Set.indicator_of_notMem hx, zero_mul]
  rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : -(1/2 : ℝ) ≤ 1/2)]
  have hleft : (∫ x : ℝ in (-(1/2 : ℝ))..0, tentDensity x) = (3/8 : ℝ) := by
    have heq : (∫ x : ℝ in (-(1/2 : ℝ))..0, tentDensity x) =
        ∫ x : ℝ in (-(1/2 : ℝ))..0, 1+x := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply tentDensity_of_mem_Icc_neg_one_zero
      simp only [uIcc_of_le (by norm_num : -(1/2 : ℝ) ≤ 0), mem_Icc] at hx
      exact ⟨by linarith [hx.1], hx.2⟩
    rw [heq, intervalIntegral.integral_comp_add_left (fun x : ℝ => x) 1]
    norm_num [integral_id]
  have hright : (∫ x : ℝ in (0 : ℝ)..(1/2 : ℝ), tentDensity x) = (3/8 : ℝ) := by
    have heq : (∫ x : ℝ in (0 : ℝ)..(1/2 : ℝ), tentDensity x) =
        ∫ x : ℝ in (0 : ℝ)..(1/2 : ℝ), 1-x := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply tentDensity_of_mem_Icc_zero_one
      simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/2), mem_Icc] at hx
      exact ⟨hx.1, by linarith [hx.2]⟩
    rw [heq, intervalIntegral.integral_comp_sub_left (fun x : ℝ => x) 1]
    norm_num [integral_id]
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (continuous_tentDensity.intervalIntegrable (-(1/2 : ℝ)) 0)
    (continuous_tentDensity.intervalIntegrable 0 (1/2 : ℝ))
  rw [hleft, hright] at hs
  linarith

theorem integral_sinc_cube :
    (∫ t : ℝ, Real.sinc (Real.pi*t)^3) = (3/4 : ℝ) := by
  have hpair :
      (∫ t : ℝ, (𝓕 (fun x => (unitBoxDensity x : ℂ)) t) *
        (Real.sinc (Real.pi*t) : ℂ)^2) =
      ∫ x : ℝ, (unitBoxDensity x : ℂ) *
        𝓕 (fun t : ℝ => (Real.sinc (Real.pi*t) : ℂ)^2) x := by
    simpa only [flip_innerₗ, smul_eq_mul] using!
      (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
        Real.continuous_fourierChar continuous_inner
        integrable_unitBoxDensity.ofReal integrable_complex_sincSquared)
  simp_rw [fourier_unitBoxDensity, fourier_sincSquared] at hpair
  have hleft :
      (fun t : ℝ => (Real.sinc (Real.pi*t) : ℂ) * (Real.sinc (Real.pi*t) : ℂ)^2) =
      fun t : ℝ => ((Real.sinc (Real.pi*t)^3 : ℝ) : ℂ) := by
    funext t
    push_cast
    ring
  have hright : (fun t : ℝ => (unitBoxDensity t : ℂ) * (tentDensity t : ℂ)) =
      fun t : ℝ => ((unitBoxDensity t * tentDensity t : ℝ) : ℂ) := by
    funext t
    push_cast
    rfl
  rw [hleft, hright, integral_complex_ofReal, integral_complex_ofReal] at hpair
  exact (Complex.ofReal_injective hpair).trans integral_unitBoxDensity_mul_tentDensity

#print axioms fourier_unitBoxDensity
#print axioms integral_sinc_cube
end CubeSections
