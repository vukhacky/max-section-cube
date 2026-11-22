import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic

/-! The actual standard Gaussian quantile and its interval transport. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace CubeSections

/-- The cumulative distribution function of the actual standard Gaussian law. -/
def standardGaussianCDF (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- The standard Gaussian quantile. Only arguments in `(0,1)` are used below. -/
def standardGaussianQuantile : ℝ → ℝ := Function.invFun standardGaussianCDF

theorem standardGaussianCDF_eq_integral (x : ℝ) :
    standardGaussianCDF x = ∫ t in Iic x, gaussianPDFReal 0 1 t := by
  rw [standardGaussianCDF, cdf_eq_real, measureReal_def,
    gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    ENNReal.toReal_ofReal]
  exact integral_nonneg (fun _ => gaussianPDFReal_nonneg _ _ _)

theorem continuous_standardGaussianPDF : Continuous (gaussianPDFReal 0 1) := by
  unfold gaussianPDFReal
  fun_prop

theorem hasDerivAt_standardGaussianCDF (x : ℝ) :
    HasDerivAt standardGaussianCDF (gaussianPDFReal 0 1 x) x := by
  have h := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := x)
    (integrable_gaussianPDFReal 0 1).intervalIntegrable
    (stronglyMeasurable_gaussianPDFReal 0 1).stronglyMeasurableAtFilter
    continuous_standardGaussianPDF.continuousAt
  have hfun : standardGaussianCDF = fun y : ℝ =>
      (∫ t in (0 : ℝ)..y, gaussianPDFReal 0 1 t) + standardGaussianCDF 0 := by
    funext y
    rw [standardGaussianCDF_eq_integral, standardGaussianCDF_eq_integral,
      ← intervalIntegral.integral_Iic_sub_Iic
        (integrable_gaussianPDFReal 0 1).integrableOn
        (integrable_gaussianPDFReal 0 1).integrableOn]
    ring
  rw [hfun]
  exact h.add_const _

theorem continuous_standardGaussianCDF : Continuous standardGaussianCDF :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_standardGaussianCDF x).continuousAt)

theorem strictMono_standardGaussianCDF : StrictMono standardGaussianCDF :=
  strictMono_of_hasDerivAt_pos hasDerivAt_standardGaussianCDF
    (fun x => gaussianPDFReal_pos 0 1 x (by norm_num))

theorem standardGaussianCDF_mem_Ioo (x : ℝ) : standardGaussianCDF x ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · exact lt_of_le_of_lt (cdf_nonneg (gaussianReal 0 1) (x - 1))
      (strictMono_standardGaussianCDF (by linarith : x - 1 < x))
  · exact lt_of_lt_of_le (strictMono_standardGaussianCDF (by linarith : x < x + 1))
      (cdf_le_one (gaussianReal 0 1) (x + 1))

theorem standardGaussianCDF_surjOn : SurjOn standardGaussianCDF univ (Ioo (0 : ℝ) 1) := by
  intro p hp
  have hlo : ∃ x : ℝ, standardGaussianCDF x < p :=
    ((tendsto_cdf_atBot (gaussianReal 0 1)).eventually (eventually_lt_nhds hp.1)).exists
  have hhi : ∃ x : ℝ, p < standardGaussianCDF x :=
    ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually (eventually_gt_nhds hp.2)).exists
  obtain ⟨x, hx⟩ := mem_range_of_exists_le_of_exists_ge continuous_standardGaussianCDF
    (hlo.imp fun _ h => h.le) (hhi.imp fun _ h => h.le)
  exact ⟨x, mem_univ _, hx⟩

theorem standardGaussianCDF_quantile {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    standardGaussianCDF (standardGaussianQuantile p) = p := by
  obtain ⟨x, _, hx⟩ := standardGaussianCDF_surjOn hp
  exact Function.invFun_eq ⟨x, hx⟩

theorem standardGaussianQuantile_CDF (x : ℝ) :
    standardGaussianQuantile (standardGaussianCDF x) = x :=
  Function.leftInverse_invFun strictMono_standardGaussianCDF.injective x

theorem strictMonoOn_standardGaussianQuantile :
    StrictMonoOn standardGaussianQuantile (Ioo (0 : ℝ) 1) := by
  intro p hp q hq hpq
  apply strictMono_standardGaussianCDF.lt_iff_lt.mp
  rwa [standardGaussianCDF_quantile hp, standardGaussianCDF_quantile hq]

theorem standardGaussianQuantile_image :
    standardGaussianQuantile '' Ioo (0 : ℝ) 1 = univ := by
  apply eq_univ_of_forall
  intro x
  exact ⟨standardGaussianCDF x, standardGaussianCDF_mem_Ioo x, standardGaussianQuantile_CDF x⟩

theorem continuousAt_standardGaussianQuantile {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt standardGaussianQuantile p := by
  apply strictMonoOn_standardGaussianQuantile.continuousAt_of_image_mem_nhds
    (isOpen_Ioo.mem_nhds hp)
  rw [standardGaussianQuantile_image]
  exact univ_mem

theorem hasDerivAt_standardGaussianQuantile {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt standardGaussianQuantile
      (gaussianPDFReal 0 1 (standardGaussianQuantile p))⁻¹ p := by
  apply HasDerivAt.of_local_left_inverse (continuousAt_standardGaussianQuantile hp)
    (hasDerivAt_standardGaussianCDF _) (ne_of_gt (gaussianPDFReal_pos 0 1 _ (by norm_num)))
  filter_upwards [isOpen_Ioo.mem_nhds hp] with q hq
  exact standardGaussianCDF_quantile hq

/-- The exact monotone transport from `(-r,r)` to the standard Gaussian line. -/
def intervalGaussianTransport (r s : ℝ) : ℝ :=
  standardGaussianQuantile ((s + r) / (2 * r))

theorem intervalGaussianTransport_argument {r s : ℝ} (hr : 0 < r) (hs : s ∈ Ioo (-r) r) :
    (s + r) / (2 * r) ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · exact div_pos (by linarith [hs.1]) (by positivity)
  · apply (div_lt_one (by positivity : 0 < 2 * r)).mpr
    linarith [hs.2]

theorem CDF_intervalGaussianTransport {r s : ℝ} (hr : 0 < r) (hs : s ∈ Ioo (-r) r) :
    standardGaussianCDF (intervalGaussianTransport r s) = (s + r) / (2 * r) :=
  standardGaussianCDF_quantile (intervalGaussianTransport_argument hr hs)

theorem strictMonoOn_intervalGaussianTransport {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (intervalGaussianTransport r) (Ioo (-r) r) := by
  intro s hs t ht hst
  exact strictMonoOn_standardGaussianQuantile
    (intervalGaussianTransport_argument hr hs) (intervalGaussianTransport_argument hr ht)
    ((div_lt_div_iff_of_pos_right (by positivity : 0 < 2 * r)).mpr (by linarith))

theorem hasDerivAt_intervalGaussianTransport {r s : ℝ} (hr : 0 < r) (hs : s ∈ Ioo (-r) r) :
    HasDerivAt (intervalGaussianTransport r)
      (2 * r * gaussianPDFReal 0 1 (intervalGaussianTransport r s))⁻¹ s := by
  have h := (hasDerivAt_standardGaussianQuantile (intervalGaussianTransport_argument hr hs)).comp s
    (((hasDerivAt_id s).add_const r).div_const (2 * r))
  change HasDerivAt (fun x => standardGaussianQuantile ((x + r) / (2 * r))) _ s
  simpa only [Function.comp_def, id_eq, intervalGaussianTransport, mul_inv_rev, one_div] using h

theorem intervalGaussianTransport_deriv_pos {r s : ℝ} (hr : 0 < r) (hs : s ∈ Ioo (-r) r) :
    0 < deriv (intervalGaussianTransport r) s := by
  rw [(hasDerivAt_intervalGaussianTransport hr hs).deriv]
  exact inv_pos.mpr (mul_pos (by positivity) (gaussianPDFReal_pos 0 1 _ (by norm_num)))

end CubeSections
