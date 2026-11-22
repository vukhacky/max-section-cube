import CubeSections.Classical.SincCubic
import CubeSections.Analysis.SincNegativeLobes

/-! A rational strict upper bound on the absolute cubic sinc integral, from
an exact signed Fourier integral and rigorously controlled negative lobes. -/
noncomputable section
namespace CubeSections

theorem ballSincIntegral_three_lt_seven_ninths : ballSincIntegral 3 < (7:ℝ)/9 := by
  rw [ballSincIntegral_three_eq_signed_add_negative, integral_sinc_cube]
  have h := sinc_negative_cube_halfline_bound
  have hc := cubic_negative_lobe_constant_lt
  linarith

theorem ballSincIntegral_three_le_seven_ninths : ballSincIntegral 3 ≤ (7:ℝ)/9 :=
  ballSincIntegral_three_lt_seven_ninths.le

#print axioms ballSincIntegral_three_lt_seven_ninths
end CubeSections
