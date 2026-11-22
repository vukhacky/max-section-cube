import CubeSections.Analysis.GaussianQuantile
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! The actual monotone Gaussian transport of a continuous strictly positive
probability density on the real line. No transport field is assumed. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff

namespace CubeSections

def densityCDF (f : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in Iic s, f t

def densityGaussianTransport (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  standardGaussianQuantile (densityCDF f s)

def densityGaussianSlope (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  f s / gaussianPDFReal 0 1 (densityGaussianTransport f s)

theorem hasDerivAt_densityCDF {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f) (x : ℝ) :
    HasDerivAt (densityCDF f) (f x) x := by
  have h := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := x)
    hi.intervalIntegrable hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hfun : densityCDF f = fun y : ℝ => (∫ t in (0 : ℝ)..y, f t) + densityCDF f 0 := by
    funext y
    rw [densityCDF, densityCDF, ← intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]
    ring
  rw [hfun]
  exact h.add_const _

theorem continuous_densityCDF {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f) :
    Continuous (densityCDF f) :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_densityCDF hc hi x).continuousAt)

theorem measurable_densityCDF {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f) :
    Measurable (densityCDF f) := (continuous_densityCDF hc hi).measurable

theorem densityCDF_nonneg {f : ℝ → ℝ} (hp : ∀ x, 0 < f x) (x : ℝ) : 0 ≤ densityCDF f x :=
  integral_nonneg (fun t => (hp t).le)

theorem densityCDF_le_one {f : ℝ → ℝ} (hi : Integrable f) (hp : ∀ x, 0 < f x)
    (hm : (∫ x, f x) = 1) (x : ℝ) : densityCDF f x ≤ 1 := by
  rw [← hm]
  exact setIntegral_le_integral hi (ae_of_all _ (fun t => (hp t).le))

theorem strictMono_densityCDF {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) : StrictMono (densityCDF f) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_densityCDF hc hi) hp

theorem densityCDF_mem_Ioo {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) (x : ℝ) : densityCDF f x ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · exact lt_of_le_of_lt (densityCDF_nonneg hp (x - 1))
      (strictMono_densityCDF hc hi hp (by linarith : x - 1 < x))
  · exact lt_of_lt_of_le (strictMono_densityCDF hc hi hp (by linarith : x < x + 1))
      (densityCDF_le_one hi hp hm (x + 1))

theorem CDF_densityGaussianTransport {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) (x : ℝ) :
    standardGaussianCDF (densityGaussianTransport f x) = densityCDF f x :=
  standardGaussianCDF_quantile (densityCDF_mem_Ioo hc hi hp hm x)

theorem strictMono_densityGaussianTransport {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) : StrictMono (densityGaussianTransport f) := by
  intro x y hxy
  exact strictMonoOn_standardGaussianQuantile (densityCDF_mem_Ioo hc hi hp hm x)
    (densityCDF_mem_Ioo hc hi hp hm y) (strictMono_densityCDF hc hi hp hxy)

theorem hasDerivAt_densityGaussianTransport {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) (x : ℝ) :
    HasDerivAt (densityGaussianTransport f) (densityGaussianSlope f x) x := by
  have h := (hasDerivAt_standardGaussianQuantile (densityCDF_mem_Ioo hc hi hp hm x)).comp x
    (hasDerivAt_densityCDF hc hi x)
  change HasDerivAt (fun t => standardGaussianQuantile (densityCDF f t)) _ x
  simpa only [densityGaussianTransport, densityGaussianSlope, Function.comp_def,
    div_eq_mul_inv, mul_comm] using h

theorem densityGaussianSlope_pos {f : ℝ → ℝ} (hp : ∀ x, 0 < f x) (x : ℝ) :
    0 < densityGaussianSlope f x :=
  div_pos (hp x) (gaussianPDFReal_pos 0 1 _ (by norm_num))

theorem continuous_densityGaussianTransport {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) : Continuous (densityGaussianTransport f) :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_densityGaussianTransport hc hi hp hm x).continuousAt)

theorem measurable_densityGaussianTransport {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) : Measurable (densityGaussianTransport f) :=
  (continuous_densityGaussianTransport hc hi hp hm).measurable

theorem continuous_densityGaussianSlope {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) : Continuous (densityGaussianSlope f) :=
  hc.div (continuous_standardGaussianPDF.comp (continuous_densityGaussianTransport hc hi hp hm))
    (fun x => ne_of_gt (gaussianPDFReal_pos 0 1 _ (by norm_num)))

theorem measurable_densityGaussianSlope {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) : Measurable (densityGaussianSlope f) :=
  (continuous_densityGaussianSlope hc hi hp hm).measurable

theorem contDiff_densityGaussianTransport {f : ℝ → ℝ} (hc : Continuous f) (hi : Integrable f)
    (hp : ∀ x, 0 < f x) (hm : (∫ x, f x) = 1) : ContDiff ℝ 1 (densityGaussianTransport f) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_densityGaussianTransport hc hi hp hm x).differentiableAt, ?_⟩
  have heq : deriv (densityGaussianTransport f) = densityGaussianSlope f :=
    funext (fun x => (hasDerivAt_densityGaussianTransport hc hi hp hm x).deriv)
  rw [heq]
  exact continuous_densityGaussianSlope hc hi hp hm

/-- The exact one-dimensional density identity needed for geometric BL. -/
theorem densityGaussianTransport_density_jacobian (f : ℝ → ℝ) (x : ℝ) :
    gaussianPDFReal 0 1 (densityGaussianTransport f x) * densityGaussianSlope f x = f x := by
  unfold densityGaussianSlope
  field_simp [ne_of_gt (gaussianPDFReal_pos 0 1 (densityGaussianTransport f x) (by norm_num))]

end CubeSections
