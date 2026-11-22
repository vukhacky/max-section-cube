import CubeSections.Analysis.FunctionalBLClosure
import CubeSections.Analysis.FrameLiftEnergy
import CubeSections.Classical.SincBrascampLieb
import CubeSections.Classical.SincIntegrability

/-! Exact specialization of continuous functional geometric BL to the
manuscript's sinc factors. Zero rows use a Gaussian probability density and
remain neutral after the zero outer exponent. Active rows use the actual
scaled sinc integral, whose finiteness and positivity are proved here without
the sharp Ball bound.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CubeSections

def scaledSincIntegrand (b t : ℝ) : ℝ :=
  ballSincIntegrand (1/b) (Real.sqrt b*t)

theorem scaledSincIntegral_eq_integral_integrand (b : ℝ) :
    scaledSincIntegral b = ∫ t, scaledSincIntegrand b t := by
  simp only [scaledSincIntegral, scaledSincIntegrand, ballSincIntegrand, mul_assoc]

theorem scaledSincIntegrand_nonneg (b t : ℝ) : 0 ≤ scaledSincIntegrand b t :=
  ballSincIntegrand_nonneg _ _

theorem continuous_scaledSincIntegrand (b : ℝ) (hb : 0 ≤ b) :
    Continuous (scaledSincIntegrand b) :=
  (continuous_ballSincIntegrand _ (div_nonneg zero_le_one hb)).comp
    (continuous_const.mul continuous_id)

theorem integrable_scaledSincIntegrand (b : ℝ) (hb : 0 < b) (hb' : b ≤ 1/2) :
    Integrable (scaledSincIntegrand b) :=
  (integrable_ballSincIntegrand _ (reciprocal_ge_two_of_le_half b hb hb')).comp_mul_left'
    (ne_of_gt (Real.sqrt_pos.2 hb))

theorem scaledSincIntegral_pos_unconditional (b : ℝ) (hb : 0 < b) (hb' : b ≤ 1/2) :
    0 < scaledSincIntegral b := by
  rw [scaledSincIntegral_eq b hb]
  exact div_pos (ballSincIntegral_pos_of_two_le _ (reciprocal_ge_two_of_le_half b hb hb'))
    (Real.sqrt_pos.2 hb)

def normalizedSincDensity (b t : ℝ) : ℝ :=
  if b=0 then gaussianPDFReal 0 1 t else scaledSincIntegrand b t/scaledSincIntegral b

theorem continuous_normalizedSincDensity (b : ℝ) (hb : 0 ≤ b) :
    Continuous (normalizedSincDensity b) := by
  change Continuous (fun t => normalizedSincDensity b t)
  by_cases hb0 : b=0
  · simpa only [normalizedSincDensity, hb0, ite_true] using continuous_standardGaussianPDF
  · simpa only [normalizedSincDensity, hb0, ite_false] using
      (continuous_scaledSincIntegrand b hb).div_const (scaledSincIntegral b)

theorem integrable_normalizedSincDensity (b : ℝ) (hb : 0 ≤ b) (hb' : b ≤ 1/2) :
    Integrable (normalizedSincDensity b) := by
  change Integrable (fun t => normalizedSincDensity b t)
  by_cases hb0 : b=0
  · simpa only [normalizedSincDensity, hb0, ite_true] using integrable_gaussianPDFReal 0 1
  · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    simpa only [normalizedSincDensity, hb0, ite_false] using
      (integrable_scaledSincIntegrand b hbp hb').div_const (scaledSincIntegral b)

theorem normalizedSincDensity_nonneg (b : ℝ) (hb : 0 ≤ b) (hb' : b ≤ 1/2) (t : ℝ) :
    0 ≤ normalizedSincDensity b t := by
  by_cases hb0 : b=0
  · simpa only [normalizedSincDensity, hb0, ite_true] using gaussianPDFReal_nonneg 0 1 t
  · simp only [normalizedSincDensity, hb0, ite_false]
    exact div_nonneg (scaledSincIntegrand_nonneg b t)
      (scaledSincIntegral_pos_unconditional b (lt_of_le_of_ne hb (Ne.symm hb0)) hb').le

theorem integral_normalizedSincDensity (b : ℝ) (hb : 0 ≤ b) (hb' : b ≤ 1/2) :
    (∫ t, normalizedSincDensity b t) = 1 := by
  by_cases hb0 : b=0
  · simp only [normalizedSincDensity, hb0, ite_true]
    exact integral_gaussianPDFReal_eq_one 0 (by norm_num : (1 : NNReal) ≠ 0)
  · simp only [normalizedSincDensity, hb0, ite_false]
    rw [integral_div, ← scaledSincIntegral_eq_integral_integrand]
    exact div_self (ne_of_gt (scaledSincIntegral_pos_unconditional b
      (lt_of_le_of_ne hb (Ne.symm hb0)) hb'))

theorem normalizedSincDensity_factor (b : ℝ) (hb : 0 ≤ b) (hb' : b ≤ 1/2) (t : ℝ) :
    (normalizedSincDensity b t)^b * (scaledSincIntegral b)^b =
      |Real.sinc (Real.pi*Real.sqrt b*t)| := by
  by_cases hb0 : b=0
  · simp [hb0]
  · have hJ := scaledSincIntegral_pos_unconditional b (lt_of_le_of_ne hb (Ne.symm hb0)) hb'
    rw [← Real.mul_rpow (normalizedSincDensity_nonneg b hb hb' t) hJ.le]
    have hcancel : normalizedSincDensity b t * scaledSincIntegral b = scaledSincIntegrand b t := by
      simp only [normalizedSincDensity, hb0, ite_false]
      exact div_mul_cancel₀ _ (ne_of_gt hJ)
    rw [hcancel]
    simp only [scaledSincIntegrand, ballSincIntegrand, mul_assoc]
    rw [← Real.rpow_mul (abs_nonneg _), one_div_mul_cancel hb0, Real.rpow_one]

theorem normalizedSincDensity_frameProduct {n d : ℕ} (W : Frame n d)
    (hW : ∀ i, leverage W i ≤ 1/2) (x : E d) :
    frameFunctionProduct W (fun i => normalizedSincDensity (leverage W i)) x *
        sincProduct (leverage W) = cubeAbsSincKernel W x := by
  simp only [frameFunctionProduct, sincProduct, cubeAbsSincKernel, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [normalizedSincDensity_factor _ (leverage_nonneg W i) (hW i)]
  congr 2
  rw [mul_assoc, normalizedFrameCoordinate_scaled]

/-- Specialization of positive continuous functional BL after the proved
Gaussian closure. This conditional bridge is discharged by the actual
positive-density transport theorem in the final wrapper. -/
theorem sincBrascampLieb_of_positiveFunctionalBL
    (hpositive : ∀ {n d : ℕ} (W : Frame n d) (g : Fin n → ℝ → ℝ),
      (∀ i, Continuous (g i)) → (∀ i, Integrable (g i)) →
      (∀ i t, 0 < g i t) → (∀ i, ∫ t, g i t = 1) →
      Integrable (frameFunctionProduct W g) ∧ (∫ x, frameFunctionProduct W g x) ≤ 1) :
    SincBrascampLiebStatement := by
  intro n d W hW
  let f : Fin n → ℝ → ℝ := fun i => normalizedSincDensity (leverage W i)
  obtain ⟨hI, hB⟩ := nonnegativeFunctionalBL_of_positive W (hpositive W) f
    (fun i => continuous_normalizedSincDensity _ (leverage_nonneg W i))
    (fun i => integrable_normalizedSincDensity _ (leverage_nonneg W i) (hW i))
    (fun i => normalizedSincDensity_nonneg _ (leverage_nonneg W i) (hW i))
    (fun i => integral_normalizedSincDensity _ (leverage_nonneg W i) (hW i))
  have heq (x : E d) : sincProduct (leverage W)*frameFunctionProduct W f x = cubeAbsSincKernel W x := by
    rw [mul_comm]
    exact normalizedSincDensity_frameProduct W hW x
  have hC : 0 ≤ sincProduct (leverage W) := by
    apply Finset.prod_nonneg
    intro i _
    exact Real.rpow_nonneg (integral_nonneg (fun t => Real.rpow_nonneg (abs_nonneg _) _)) _
  refine ⟨(hI.const_mul _).congr (ae_of_all _ heq), ?_⟩
  calc
    (∫ x, cubeAbsSincKernel W x) = ∫ x, sincProduct (leverage W)*frameFunctionProduct W f x :=
      integral_congr_ae (ae_of_all _ (fun x => (heq x).symm))
    _ = sincProduct (leverage W)*(∫ x, frameFunctionProduct W f x) := integral_const_mul _ _
    _ ≤ sincProduct (leverage W)*1 := mul_le_mul_of_nonneg_left hB hC
    _ = sincProduct (leverage W) := mul_one _

#print axioms sincBrascampLieb_of_positiveFunctionalBL
end CubeSections
