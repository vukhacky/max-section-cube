import CubeSections.Analysis.GaussianQuantile

/-! Global measurable versions of the actual Gaussian quantiles. -/

noncomputable section
open Set

namespace CubeSections

theorem standardGaussianQuantile_outside {p : ℝ} (hp : p ∉ Ioo (0 : ℝ) 1) :
    standardGaussianQuantile p = Classical.arbitrary ℝ := by
  apply Function.invFun_neg
  rintro ⟨x, hx⟩
  apply hp
  rw [← hx]
  exact standardGaussianCDF_mem_Ioo x

@[fun_prop] theorem measurable_standardGaussianQuantile : Measurable standardGaussianQuantile := by
  classical
  have hc : ContinuousOn standardGaussianQuantile (Ioo (0 : ℝ) 1) :=
    fun p hp => (continuousAt_standardGaussianQuantile hp).continuousWithinAt
  have heq : standardGaussianQuantile = (Ioo (0 : ℝ) 1).piecewise standardGaussianQuantile
      (fun _ => Classical.arbitrary ℝ) := by
    funext p
    by_cases hp : p ∈ Ioo (0 : ℝ) 1
    · simp [hp]
    · simp [hp, standardGaussianQuantile_outside hp]
  rw [heq]
  exact hc.measurable_piecewise continuousOn_const measurableSet_Ioo

@[fun_prop] theorem measurable_intervalGaussianTransport (r : ℝ) :
    Measurable (intervalGaussianTransport r) := by
  unfold intervalGaussianTransport
  fun_prop

end CubeSections
