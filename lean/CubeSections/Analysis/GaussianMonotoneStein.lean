import CubeSections.Analysis.GaussianSteinGeneral
import CubeSections.Analysis.BoundedMonotoneDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Function.L2Space

/-! Automatic Gaussian integrability of a nonnegative derivative. Bounded
arctangent saturations have integrable derivatives by ordinary FTC. Stein for
the saturations gives a uniform L1 bound; Fatou removes the saturation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace CubeSections

theorem integrable_gaussian_of_integrable {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable f (gaussianReal 0 1) := by
  apply (integrable_standardGaussian_density_iff f).mpr
  apply hf.bdd_mul continuous_standardGaussianPDF.aestronglyMeasurable
    (c := (Real.sqrt (2*Real.pi))⁻¹)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x)]
    simp only [gaussianPDFReal_def, NNReal.coe_one, sub_zero, mul_one]
    calc
      _ ≤ (Real.sqrt (2*Real.pi))⁻¹ * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])) (by positivity)
      _ = _ := mul_one _)

theorem abs_arctan_le_abs (x : ℝ) : |Real.arctan x| ≤ |x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.arctan) (f' := fun y : ℝ => 1/(1+y^2)) (C := 1)
    (s := (univ : Set ℝ)) (fun y _ => (Real.hasDerivAt_arctan y).hasDerivWithinAt)
    (fun y _ => by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1/(1+y^2))]
      apply (div_le_one (by positivity : 0 < 1+y^2)).mpr
      nlinarith [sq_nonneg y]) convex_univ (x := 0) (y := x) (mem_univ _) (mem_univ _)
  simpa only [Real.arctan_zero, sub_zero, one_mul, Real.norm_eq_abs] using h

def monotoneSaturation (g : ℝ → ℝ) (R : ℝ) (x : ℝ) : ℝ :=
  R * Real.arctan (g x / R)

def monotoneSaturationDerivative (g g' : ℝ → ℝ) (R : ℝ) (x : ℝ) : ℝ :=
  g' x / (1 + (g x / R)^2)

theorem hasDerivAt_monotoneSaturation {g g' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt g (g' x) x) (R : ℝ) (hR : R ≠ 0) (x : ℝ) :
    HasDerivAt (monotoneSaturation g R) (monotoneSaturationDerivative g g' R x) x := by
  convert (((hd x).div_const R).arctan.const_mul R) using 1
  · rfl
  · unfold monotoneSaturationDerivative
    field_simp

theorem monotoneSaturation_abs_le (g : ℝ → ℝ) {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |monotoneSaturation g R x| ≤ |g x| := by
  unfold monotoneSaturation
  rw [abs_mul, abs_of_pos hR]
  calc
    _ ≤ R * |g x/R| := mul_le_mul_of_nonneg_left (abs_arctan_le_abs _) hR.le
    _ = |g x| := by rw [abs_div, abs_of_pos hR]; field_simp

theorem monotoneSaturation_bounded (g : ℝ → ℝ) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, ∀ x, |monotoneSaturation g R x| ≤ C := by
  refine ⟨R*(Real.pi/2), fun x => ?_⟩
  unfold monotoneSaturation
  rw [abs_mul, abs_of_pos hR]
  apply mul_le_mul_of_nonneg_left _ hR.le
  exact abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le,
    (Real.arctan_lt_pi_div_two _).le⟩

theorem monotoneSaturationDerivative_nonneg (g g' : ℝ → ℝ)
    (hp : ∀ x, 0 ≤ g' x) (R : ℝ) (x : ℝ) :
    0 ≤ monotoneSaturationDerivative g g' R x :=
  div_nonneg (hp x) (by positivity)

theorem integrable_monotoneSaturationDerivative {g g' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt g (g' x) x) (hp : ∀ x, 0 ≤ g' x)
    {R : ℝ} (hR : 0 < R) :
    Integrable (monotoneSaturationDerivative g g' R) (gaussianReal 0 1) := by
  apply integrable_gaussian_of_integrable
  exact integrable_nonneg_deriv_of_bounded (monotoneSaturation g R)
    (monotoneSaturationDerivative g g' R) (hasDerivAt_monotoneSaturation hd R (ne_of_gt hR))
    (monotoneSaturationDerivative_nonneg g g' hp R) (monotoneSaturation_bounded g hR)

theorem integral_monotoneSaturationDerivative_le {g g' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt g (g' x) x) (hp : ∀ x, 0 ≤ g' x)
    (hg : Integrable g (gaussianReal 0 1))
    (hxg : Integrable (fun x => x*g x) (gaussianReal 0 1))
    {R : ℝ} (hR : 0 < R) :
    (∫ x, monotoneSaturationDerivative g g' R x ∂gaussianReal 0 1) ≤
      ∫ x, |x*g x| ∂gaussianReal 0 1 := by
  have hc : Continuous (monotoneSaturation g R) :=
    continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_monotoneSaturation hd R (ne_of_gt hR) x).continuousAt)
  have hi : Integrable (monotoneSaturation g R) (gaussianReal 0 1) :=
    hg.abs.mono' hc.aestronglyMeasurable (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs]
      exact monotoneSaturation_abs_le g hR x))
  have hpoint (x : ℝ) : |x*monotoneSaturation g R x| ≤ |x*g x| := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (monotoneSaturation_abs_le g hR x) (abs_nonneg x)
  have hxi : Integrable (fun x => x*monotoneSaturation g R x) (gaussianReal 0 1) :=
    hxg.abs.mono' (continuous_id.mul hc).aestronglyMeasurable
      (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact hpoint x))
  rw [gaussian_stein_of_integrable (hasDerivAt_monotoneSaturation hd R (ne_of_gt hR)) hi
    (integrable_monotoneSaturationDerivative hd hp hR) hxi]
  exact integral_mono hxi hxg.abs (fun x => (le_abs_self _).trans (hpoint x))

theorem monotoneSaturationDerivative_tendsto (g g' : ℝ → ℝ) (x : ℝ) :
    Tendsto (fun m : ℕ => monotoneSaturationDerivative g g' ((m:ℝ)+1) x) atTop
      (𝓝 (g' x)) := by
  have hm : Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun m : ℕ => g x/((m:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hm
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => g' x) atTop (𝓝 (g' x))).div
    (tendsto_const_nhds.add (hsmall.pow 2)) (by norm_num : (1:ℝ)+0^2 ≠ 0)
  have h' : Tendsto (fun m : ℕ => g' x/(1+(g x/((m:ℝ)+1))^2)) atTop
      (𝓝 (g' x/(1+(0:ℝ)^2))) :=
    h.congr' (Eventually.of_forall (fun m => rfl))
  simpa only [monotoneSaturationDerivative, zero_pow (by decide : 2≠0), add_zero, div_one] using h'

theorem integrable_gaussian_id_mul_of_memLp_two {g : ℝ → ℝ}
    (hg : MemLp g 2 (gaussianReal 0 1)) :
    Integrable (fun x => x*g x) (gaussianReal 0 1) := by
  have hx : MemLp id (2:ℝ≥0∞) (gaussianReal 0 1) := by
    simpa using memLp_id_gaussianReal (μ := 0) (v := 1) (2:ℝ≥0)
  exact (hx.integrable_mul hg).congr (ae_of_all _ (fun x => rfl))

theorem integrable_gaussian_deriv_of_nonneg (g g' : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt g (g' x) x) (hnonneg : ∀ x, 0 ≤ g' x)
    (hg : MemLp g 2 (gaussianReal 0 1)) : Integrable g' (gaussianReal 0 1) := by
  have hgi : Integrable g (gaussianReal 0 1) := hg.integrable (by norm_num)
  have hxg : Integrable (fun x => x*g x) (gaussianReal 0 1) :=
    integrable_gaussian_id_mul_of_memLp_two hg
  have hR (m : ℕ) : (0:ℝ) < (m:ℝ)+1 := by positivity
  have hI (m : ℕ) := integrable_monotoneSaturationDerivative hd hnonneg (hR m)
  have hb (m : ℕ) :
      (∫⁻ x, ‖monotoneSaturationDerivative g g' ((m:ℝ)+1) x‖ₑ ∂gaussianReal 0 1) ≤
        ENNReal.ofReal (∫ x, |x*g x| ∂gaussianReal 0 1) := by
    rw [← ofReal_integral_norm_eq_lintegral_eNorm (hI m)]
    apply ENNReal.ofReal_le_ofReal
    have heq : (∫ x, ‖monotoneSaturationDerivative g g' ((m:ℝ)+1) x‖ ∂gaussianReal 0 1) =
        ∫ x, monotoneSaturationDerivative g g' ((m:ℝ)+1) x ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => Real.norm_of_nonneg (monotoneSaturationDerivative_nonneg g g' hnonneg _ x))
    rw [heq]
    exact integral_monotoneSaturationDerivative_le hd hnonneg hgi hxg (hR m)
  apply integrable_of_tendsto
    (ae_of_all _ (monotoneSaturationDerivative_tendsto g g'))
    (fun m => (hI m).aestronglyMeasurable)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (liminf_le_of_frequently_le' (Frequently.of_forall hb))

theorem gaussian_monotone_stein (g g' : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt g (g' x) x) (hnonneg : ∀ x, 0 ≤ g' x)
    (hg : MemLp g 2 (gaussianReal 0 1)) :
    (∫ x, g' x ∂gaussianReal 0 1) = ∫ x, x*g x ∂gaussianReal 0 1 := by
  exact gaussian_stein_of_integrable hd (hg.integrable (by norm_num))
    (integrable_gaussian_deriv_of_nonneg g g' hd hnonneg hg)
    (integrable_gaussian_id_mul_of_memLp_two hg)

#print axioms integrable_gaussian_deriv_of_nonneg
#print axioms gaussian_monotone_stein
end CubeSections
